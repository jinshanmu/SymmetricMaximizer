module

public import SymmetricMaximizer.SelectionChernNumber
public import SymmetricMaximizer.SelectionCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# The common zero and the selection lemma

The nonzero top Chern number gives a zero of the five scalar section
coordinates. At the flag represented by that zero the three original
bundle components vanish. Their vanishing gives the required rank and
restrictions of the alternating forms.
-/

@[expose] public section

open Module Submodule
open scoped BigOperators InnerProductSpace LinearAlgebra.Projectivization

namespace SymmetricMaximizer.Geometry

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

private theorem exists_sectionCoordinates_zero (D : W ≃ₗ[ℂ] (Fin 3 → Fin 2 → ℂ))
    (B : End ℂ W) (α β : LinearMap.BilinForm ℂ W) :
    ∃ x, ∀ j, sectionCoordinates D B α β j x = 0 := by
  refine exists_section_zero_of_chernIntegral_ne_zero selectionConnection_laws
    (sectionCoordinates_phaseSection D B α β) ?_
  change integrateTop projectiveBox selectionChernForm ≠ 0
  rw [integral_selectionChernForm]
  exact mul_ne_zero (by norm_num) (by positivity)

variable (E : Fin 3 → Submodule ℂ W) (hindep : iSupIndep E) (htop : (⨆ i, E i) = ⊤)
variable (basis : ∀ i, Basis (Fin 2) ℂ (E i))

local notation "D" => blockCoordinates E hindep htop basis

private noncomputable def polarBase (x : Coordinates 10) : SelectionBase E :=
  fun i =>
    Projectivization.mk ℂ ⟨baseFrame D x i, blockCoordinates_baseFrame E hindep htop basis x i⟩
      (fun h => baseFrame_ne_zero D x i (congrArg Subtype.val h))

omit [FiniteDimensional ℂ W] in
private theorem polarPlane_eq_span (x : Coordinates 10) :
    selectionPlane (polarBase E hindep htop basis x) = span ℂ (Set.range (baseFrame D x)) := by
  simp [polarBase, selectionPlane, span_range_eq_iSup, Submodule.map_span]

private noncomputable def polarFlag (x : Coordinates 10) : SelectionProjectivization E :=
  ⟨(polarBase E hindep htop basis x, Projectivization.mk ℂ (tautFrame D x) (tautFrame_ne_zero D x)),
    by
      rw [Projectivization.submodule_mk, span_singleton_le_iff_mem, polarPlane_eq_span]
      exact tautFrame_mem_span D x⟩

private theorem polarCoordinates_zero (B : End ℂ W) (α β : LinearMap.BilinForm ℂ W)
    (hα : α.IsAlt) (hβ : β.IsAlt) (x : Coordinates 10)
    (hz : ∀ j, sectionCoordinates D B α β j x = 0) :
    IsSelectionZero B α β (polarFlag E hindep htop basis x) := by
  let z := polarFlag E hindep htop basis x
  let L := selectionPlane z.val.1
  let T := selectionLine z
  let u := baseFrame D x
  let X := tautFrame D x
  let l : W →ₗ[ℂ] ℂ := (innerSL ℂ X).toLinearMap
  have hL : L = span ℂ (Set.range u) := polarPlane_eq_span E hindep htop basis x
  have hXL : X ∈ L := hL.symm ▸ tautFrame_mem_span D x
  have hXT : (⟨X, hXL⟩ : L) ∈ T := mem_span_singleton_self X
  have hlX : l X ≠ 0 := mt (inner_self_eq_zero (𝕜 := ℂ)).mp (tautFrame_ne_zero D x)
  have hl (v : L) (hv : v ∈ Tᗮ) : l (v : W) = 0 :=
    (T.mem_orthogonal v).mp hv ⟨X, hXL⟩ hXT
  have hquotient (k : Fin 3) :
      quotientCoordinate (baseRepresentative k x) (D (B X) k) = 0 := by
    have hk : (⟨k.val, by omega⟩ : Fin 5).val < 3 := k.isLt
    simpa only [sectionCoordinates, dite_eq_left hk] using hz ⟨k.val, by omega⟩
  have hBX : B X ∈ L := by
    choose a ha using fun k =>
      (quotientCoordinate_eq_zero (baseRepresentative_ne_zero k x)).mp (hquotient k)
    rw [hL, mem_span_range_iff_exists_fun ℂ]
    refine ⟨a, LinearEquiv.injective D (funext fun k => ?_)⟩
    rw [coordinates_sum_frame D x a k, ha]
  have hα₀ : threeForm l α hα u = 0 := by
    have h := hz 3
    change formComponent α X u u = 0 at h
    exact h
  let P : W →ₗ[ℂ] W := Lᗮ.starProjection.toLinearMap ∘ₗ B
  let γ := β.comp P P
  have hγ : γ.IsAlt := isAlt_pullback β hβ P
  have hres (k : Fin 3) : frameResidual u (B (u k)) = P (u k) := by
    rw [frameResidual_eq_projection (linearIndependent_baseFrame D x), ← hL]
    rfl
  have hγ₀ : threeForm l γ hγ u = 0 := by
    have h := hz 4
    change formComponent β X u (fun k => frameResidual u (B (u k))) = 0 at h
    simp only [formComponent, hres] at h
    rw [threeForm_apply]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    change (v : W) ∈ ℂ ∙ X at hv
    obtain ⟨a, ha⟩ := mem_span_singleton.mp hv
    apply LinearMap.mem_ker.mpr
    change Lᗮ.orthogonalProjectionOnto (B (v : W)) = 0
    apply orthogonalProjectionOnto_orthogonal_apply_eq_zero
    rw [← ha, map_smul]
    exact L.smul_mem a hBX
  · intro v hv w hw
    exact form_zero_on_hyperplane l α hα u hα₀ (hL ▸ hXL) (hL ▸ v.property)
      (hL ▸ w.property) hlX (hl v hv) (hl w hw)
  · intro v hv w hw
    change γ (v : W) (w : W) = 0
    exact form_zero_on_hyperplane l γ hγ u hγ₀ (hL ▸ hXL) (hL ▸ v.property)
      (hL ▸ w.property) hlX (hl v hv) (hl w hw)

end SymmetricMaximizer.Geometry

namespace SymmetricMaximizer

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- The manuscript's section on the projectivization has a common zero. -/
theorem selectionSectionHasZero : SelectionSectionHasZero W := by
  intro E hindep htop hdim B α β hα hβ
  let basis (i : Fin 3) : Basis (Fin 2) ℂ (E i) :=
    ((stdOrthonormalBasis ℂ (E i)).reindex (finCongr (hdim i))).toBasis
  obtain ⟨x, hx⟩ := Geometry.exists_sectionCoordinates_zero
    (Geometry.blockCoordinates E hindep htop basis) B α β
  let z := Geometry.polarFlag E hindep htop basis x
  exact ⟨z, (selectionSectionValue_eq_zero_iff B α β hα hβ z).mpr
    (Geometry.polarCoordinates_zero E hindep htop basis B α β hα hβ x hx)⟩

/-- The three lines selected in the manuscript's selection lemma. -/
theorem exists_selectionPlane (E : Fin 3 → Submodule ℂ W) (hindep : iSupIndep E)
    (htop : (⨆ i, E i) = ⊤) (hdim : ∀ i, finrank ℂ (E i) = 2)
    (B : End ℂ W) (α β : LinearMap.BilinForm ℂ W) (hα : α.IsAlt) (hβ : β.IsAlt) :
    ∃ p : SelectionBase E,
      let L := selectionPlane p
      let g := compression B L
      finrank ℂ (LinearMap.range g) ≤ 2 ∧
      (∀ x ∈ (LinearMap.ker g)ᗮ, ∀ y ∈ (LinearMap.ker g)ᗮ, α (x : W) (y : W) = 0) ∧
      (∀ u ∈ LinearMap.range g, ∀ v ∈ LinearMap.range g, β (u : W) (v : W) = 0) := by
  obtain ⟨z, hz⟩ := selectionSectionHasZero (W := W) E hindep htop hdim B α β hα hβ
  obtain ⟨hg, ha, hb⟩ := (selectionSectionValue_eq_zero_iff B α β hα hβ z).mp hz
  exact ⟨z.val.1, selection_conclusions_of_section_zero B α β (selectionPlane z.val.1)
    (selectionLine z) (finrank_selectionPlane hindep z.val.1) (finrank_selectionLine z) hg ha hb⟩

end SymmetricMaximizer
