module

public import SymmetricMaximizer.Selection
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Topology.Algebra.Projectivization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic

/-!
# The projective space of flags in the selection lemma

The base is the product of the projective spaces of the three summands.
The total space of the projectivization has a compact model given by the
incidence condition that the last line lies in the sum of the first three.
-/

@[expose] public section

open Module Submodule
open scoped BigOperators LinearAlgebra.Projectivization

namespace SymmetricMaximizer

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The product of the projective spaces of the three summands. -/
abbrev SelectionBase (E : Fin 3 → Submodule ℂ W) := ∀ i, ℙ ℂ (E i)

/-- The fiber of the sum of the tautological lines over a base point. -/
noncomputable def selectionPlane {E : Fin 3 → Submodule ℂ W} (p : SelectionBase E) : Submodule ℂ W :=
  ⨆ i, (p i).submodule.map (E i).subtype

/-- The projectivization of the sum of the tautological lines, with its incidence topology. -/
abbrev SelectionProjectivization (E : Fin 3 → Submodule ℂ W) :=
  {p : SelectionBase E × ℙ ℂ W // p.2.submodule ≤ selectionPlane p.1}

/-- The tautological line, viewed as a subspace of the three-plane at the flag. -/
noncomputable def selectionLine {E : Fin 3 → Submodule ℂ W} (z : SelectionProjectivization E) :
    Submodule ℂ (selectionPlane z.val.1) :=
  z.val.2.submodule.comap (selectionPlane z.val.1).subtype

theorem finrank_selectionLine {E : Fin 3 → Submodule ℂ W} (z : SelectionProjectivization E) :
    finrank ℂ (selectionLine z) = 1 :=
  (Submodule.comapSubtypeEquivOfLe z.property).finrank_eq.trans z.val.2.finrank_submodule

/-- The tautological inclusion is nonzero at every flag. -/
theorem selectionLine_subtype_ne_zero {E : Fin 3 → Submodule ℂ W} (z : SelectionProjectivization E) :
    (selectionLine z).subtype ≠ 0 := by
  intro h
  have hbot : selectionLine z = ⊥ := by
    rw [← (selectionLine z).range_subtype, h, LinearMap.range_zero]
  have hd := finrank_selectionLine z
  rw [hbot, finrank_bot] at hd
  exact Nat.zero_ne_one hd

theorem selectionPlane_eq_span {E : Fin 3 → Submodule ℂ W} (p : SelectionBase E) :
    selectionPlane p = Submodule.span ℂ (Set.range fun i => ((p i).rep : W)) := by
  simp [selectionPlane, Submodule.span_range_eq_iSup, Projectivization.submodule_eq,
    Submodule.map_span]

theorem finrank_selectionPlane {E : Fin 3 → Submodule ℂ W} (hE : iSupIndep E)
    (p : SelectionBase E) : finrank ℂ (selectionPlane p) = 3 := by
  have h : LinearIndependent ℂ (fun i => ((p i).rep : W)) :=
    hE.linearIndependent E (fun i => (p i).rep.property)
      (fun i => Subtype.coe_injective.ne (p i).rep_ne_zero)
  rw [selectionPlane_eq_span, finrank_span_eq_card h, Fintype.card_fin]

/-- The orthogonal complement of the tautological line inside the selected three-plane. -/
noncomputable abbrev selectionComplement {E : Fin 3 → Submodule ℂ W}
    (z : SelectionProjectivization E) :
    Submodule ℂ (selectionPlane z.val.1) :=
  (selectionLine z)ᗮ

/-- The fiber of the bundle of the three section components, using the orthogonal model of
the quotient and the second exterior power of the complement. -/
abbrev SelectionFiber {E : Fin 3 → Submodule ℂ W} (z : SelectionProjectivization E) :=
  (selectionLine z →ₗ[ℂ] ↥(selectionPlane z.val.1)ᗮ) ×
    Module.Dual ℂ (⋀[ℂ]^2 ↥(selectionComplement z)) ×
    Module.Dual ℂ (⋀[ℂ]^2 ↥(selectionComplement z))

/-- The section takes values in a five-dimensional complex vector space at every flag. -/
theorem finrank_selectionFiber [FiniteDimensional ℂ W] (hW : finrank ℂ W = 6)
    {E : Fin 3 → Submodule ℂ W} (hE : iSupIndep E) (z : SelectionProjectivization E) :
    finrank ℂ (SelectionFiber z) = 5 := by
  have hL := finrank_selectionPlane hE z.val.1
  have hT := finrank_selectionLine z
  have hQ : finrank ℂ ↥(selectionPlane z.val.1)ᗮ = 3 := by
    have h := (selectionPlane z.val.1).finrank_add_finrank_orthogonal
    omega
  have hH : finrank ℂ (selectionComplement z) = 2 := by
    have h := (selectionLine z).finrank_add_finrank_orthogonal
    change finrank ℂ ↥(selectionLine z)ᗮ = 2
    omega
  change finrank ℂ ((selectionLine z →ₗ[ℂ] ↥(selectionPlane z.val.1)ᗮ) ×
    Module.Dual ℂ (⋀[ℂ]^2 ↥(selectionComplement z)) ×
      Module.Dual ℂ (⋀[ℂ]^2 ↥(selectionComplement z))) = 5
  simp [Module.finrank_prod, Module.finrank_linearMap, Module.Dual, hT, hQ, hH]

/-- View an alternating bilinear form as a two-argument alternating map. -/
def formToAlternating {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ω : LinearMap.BilinForm ℂ V) (hω : ω.IsAlt) : AlternatingMap ℂ V ℂ (Fin 2) where
  toFun v := ω (v 0) (v 1)
  map_update_add' m i x y := by
    fin_cases i <;> simp
  map_update_smul' m i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h ▸ hω _
    · exact h ▸ hω _
    · exact (hij rfl).elim

private theorem formToAlternating_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ω : LinearMap.BilinForm ℂ V) (hω : ω.IsAlt) :
    formToAlternating ω hω = 0 ↔ ∀ x y, ω x y = 0 := by
  constructor
  · intro h x y
    exact DFunLike.congr_fun h ![x, y]
  · intro h
    ext v
    exact h (v 0) (v 1)

/-- Pulling back a bilinear form along the same map in both arguments preserves alternation. -/
theorem isAlt_pullback {V X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ω : LinearMap.BilinForm ℂ V) (hω : ω.IsAlt) (f : X →ₗ[ℂ] V) : (ω.comp f f).IsAlt :=
  fun x => hω (f x)

/-- The value of the section given by the restricted compression, the restricted form, and
the pullback of the second form. -/
noncomputable def selectionSectionValue [FiniteDimensional ℂ W] {E : Fin 3 → Submodule ℂ W}
    (B : Module.End ℂ W) (α β : LinearMap.BilinForm ℂ W) (hα : α.IsAlt) (hβ : β.IsAlt)
    (z : SelectionProjectivization E) : SelectionFiber z :=
  let L := selectionPlane z.val.1
  let T := selectionLine z
  let H := selectionComplement z
  let g := compression B L
  let incl := L.subtype ∘ₗ H.subtype
  let inclG := Lᗮ.subtype ∘ₗ g ∘ₗ H.subtype
  ⟨g ∘ₗ T.subtype,
    exteriorPower.alternatingMapLinearEquiv (formToAlternating (α.comp incl incl) (isAlt_pullback α hα incl)),
    exteriorPower.alternatingMapLinearEquiv (formToAlternating (β.comp inclG inclG)
      (isAlt_pullback β hβ inclG))⟩

/-- Vanishing of the compression on the tautological line and of both forms on its complement. -/
def IsSelectionZero [FiniteDimensional ℂ W] {E : Fin 3 → Submodule ℂ W}
    (B : Module.End ℂ W) (α β : LinearMap.BilinForm ℂ W) (z : SelectionProjectivization E) : Prop :=
  let L := selectionPlane z.val.1
  let T := selectionLine z
  let H := Submodule.orthogonal (𝕜 := ℂ) (E := L) T
  let g := compression B L
  T ≤ LinearMap.ker g ∧
    (∀ x ∈ H, ∀ y ∈ H, α (x : W) (y : W) = 0) ∧
    (∀ x ∈ H, ∀ y ∈ H, β ((g x : Lᗮ) : W) ((g y : Lᗮ) : W) = 0)

theorem selectionSectionValue_eq_zero_iff [FiniteDimensional ℂ W] {E : Fin 3 → Submodule ℂ W}
    (B : Module.End ℂ W) (α β : LinearMap.BilinForm ℂ W) (hα : α.IsAlt) (hβ : β.IsAlt)
    (z : SelectionProjectivization E) :
    selectionSectionValue B α β hα hβ z = 0 ↔ IsSelectionZero B α β z := by
  change (_, _, _) = (0, 0, 0) ↔ _
  simp only [Prod.mk.injEq, LinearEquiv.map_eq_zero_iff, IsSelectionZero]
  rw [formToAlternating_eq_zero, formToAlternating_eq_zero]
  constructor
  · rintro ⟨hg, ha, hb⟩
    refine ⟨?_, fun x hx y hy => ha ⟨x, hx⟩ ⟨y, hy⟩, fun x hx y hy => hb ⟨x, hx⟩ ⟨y, hy⟩⟩
    intro x hx
    exact LinearMap.mem_ker.mpr (DFunLike.congr_fun hg ⟨x, hx⟩)
  · rintro ⟨hg, ha, hb⟩
    refine ⟨?_, fun x y => ha x x.property y y.property, fun x y => hb x x.property y y.property⟩
    apply LinearMap.ext
    intro x
    exact LinearMap.mem_ker.mp (hg x.property)

/-- The common zero required in the proof of `lem:selection`. -/
def SelectionSectionHasZero (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] : Prop :=
  ∀ (E : Fin 3 → Submodule ℂ W), iSupIndep E → (⨆ i, E i) = ⊤ →
    (∀ i, finrank ℂ (E i) = 2) →
    ∀ (B : Module.End ℂ W) (α β : LinearMap.BilinForm ℂ W)
      (hα : α.IsAlt) (hβ : β.IsAlt),
      ∃ z : SelectionProjectivization E, selectionSectionValue B α β hα hβ z = 0

private theorem sphere_vector_ne_zero {V : Type*} [NormedAddCommGroup V]
    (v : Metric.sphere (0 : V) 1) : (v : V) ≠ 0 := by
  have h : ‖(v : V)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  intro hv
  simp [hv] at h

private theorem exists_unit_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (x : V) (hx : x ≠ 0) : ∃ v : Metric.sphere (0 : V) 1, ∃ a : ℂ, a • (v : V) = x := by
  refine ⟨⟨(‖x‖⁻¹ : ℂ) • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩, ‖x‖, ?_⟩
  have hn : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  change (‖x‖ : ℂ) • ((‖x‖ : ℂ)⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

private theorem exists_unit_representative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (p : ℙ ℂ V) : ∃ v : Metric.sphere (0 : V) 1,
      Projectivization.mk ℂ (v : V) (sphere_vector_ne_zero v) = p := by
  obtain ⟨v, a, ha⟩ := exists_unit_smul p.rep p.rep_ne_zero
  refine ⟨v, ?_⟩
  rw [← p.mk_rep]
  exact ((Projectivization.mk_eq_mk_iff' ℂ _ _ p.rep_ne_zero (sphere_vector_ne_zero v)).mpr
    ⟨a, ha⟩).symm

private theorem plane_eq_span {E : Fin 3 → Submodule ℂ W}
    (v : ∀ i, Metric.sphere (0 : E i) 1) :
    selectionPlane (fun i => Projectivization.mk ℂ (v i : E i) (sphere_vector_ne_zero (v i))) =
      Submodule.span ℂ (Set.range fun i => ((v i : E i) : W)) := by
  simp [selectionPlane, Submodule.span_range_eq_iSup, Submodule.map_span]

/-- The total space `Z` in the selection lemma is compact. -/
theorem selectionProjectivization_compactSpace [FiniteDimensional ℂ W]
    (E : Fin 3 → Submodule ℂ W) (hE : iSupIndep E) :
    CompactSpace (SelectionProjectivization E) := by
  classical
  let V := ∀ i, Metric.sphere (0 : E i) 1
  let D := Metric.sphere (0 : Fin 3 → ℂ) 1
  let v (a : V) (i : Fin 3) : W := ((a i : E i) : W)
  let p (a : V) : SelectionBase E :=
    fun i => Projectivization.mk ℂ (a i : E i) (sphere_vector_ne_zero (a i))
  let x (a : V) (c : Fin 3 → ℂ) := ∑ i, c i • v a i
  have hx (a : V) (c : D) : x a c ≠ 0 := by
    have hv : LinearIndependent ℂ (v a) :=
      hE.linearIndependent E (fun i => (a i : E i).property)
        (fun i => Subtype.coe_injective.ne (sphere_vector_ne_zero (a i)))
    intro h
    exact sphere_vector_ne_zero c (funext ((Fintype.linearIndependent_iff.mp hv) c h))
  let f (s : V × D) : SelectionProjectivization E :=
    ⟨(p s.1, Projectivization.mk ℂ (x s.1 s.2) (hx s.1 s.2)), by
      rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem, plane_eq_span]
      exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨s.2, rfl⟩⟩
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_pi fun i => Projectivization.continuous_mk (by fun_prop) _
    · refine Projectivization.continuous_mk (K := ℂ) (f := fun s : V × D => x s.1 s.2) ?_ _
      dsimp only [x, v]
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
          (continuous_subtype_val.comp
            (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)))
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨⟨q, t⟩, hqt⟩ := z
    choose a ha using fun i => exists_unit_representative (q i)
    have hp : p a = q := funext ha
    have ht : t.rep ∈ selectionPlane (p a) := by
      rw [hp]
      apply hqt
      rw [t.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    rw [plane_eq_span] at ht
    obtain ⟨c, hct⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ht
    have hc₀ : c ≠ 0 := by
      intro he
      exact t.rep_ne_zero (by simpa [he] using hct.symm)
    obtain ⟨u, b, hb⟩ := exists_unit_smul c hc₀
    refine ⟨(a, u), Subtype.ext (Prod.ext hp ?_)⟩
    change Projectivization.mk ℂ (x a u) (hx a u) = t
    rw [← t.mk_rep]
    refine ((Projectivization.mk_eq_mk_iff' ℂ _ _ t.rep_ne_zero (hx a u)).mpr ⟨b, ?_⟩).symm
    change x a c = t.rep at hct
    rw [← hct, ← hb]
    simp [x, Finset.smul_sum, mul_smul]
  exact Function.Surjective.compactSpace hc hs

end SymmetricMaximizer
