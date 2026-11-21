module

public import SymmetricMaximizer.AlternatingHyperplane
public import SymmetricMaximizer.ChernObstruction
public import SymmetricMaximizer.ProjectiveConnections
public import SymmetricMaximizer.ProjectiveFrame
public import SymmetricMaximizer.SelectionProjectivization
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Tactic

/-!
# The five scalar coordinates of the selection section

The first three coordinates use the determinant to identify the quotient of
each two-plane by its line with the dual of that line. The last two evaluate
the wedge of the tautological covector with the relevant alternating form.
-/

@[expose] public section

open Module Submodule
open scoped ContDiff InnerProductSpace

namespace SymmetricMaximizer.Geometry

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- Determinant coordinate of a two-form on the orthogonal complement of a line. -/
noncomputable def formComponent (α : LinearMap.BilinForm ℂ W) (X : W) (u w : Fin 3 → W) : ℂ :=
  inner ℂ X (u 0) * α (w 1) (w 2) - inner ℂ X (u 1) * α (w 0) (w 2) +
    inner ℂ X (u 2) * α (w 0) (w 1)

private theorem formComponent_smul (α : LinearMap.BilinForm ℂ W) (X : W) (u w : Fin 3 → W)
    (c : ℂ) (z : Fin 3 → ℂ) :
    formComponent α (c • X) (fun i => z i • u i) (fun i => z i • w i) =
      (star c * z 0 * z 1 * z 2) * formComponent α X u w := by
  simp only [formComponent, inner_smul_left, inner_smul_right, map_smul, LinearMap.smul_apply,
    show (starRingEnd ℂ) c = star c from rfl, smul_eq_mul]
  ring

variable (D : W ≃ₗ[ℂ] (Fin 3 → Fin 2 → ℂ)) (B : End ℂ W)
variable (α β : LinearMap.BilinForm ℂ W)

/-- Values of the three quotient-line factors and two determinant-line factors on the lift. -/
noncomputable def sectionCoordinates (j : Fin 5) (x : Coordinates 10) : ℂ :=
  if h : j.val < 3 then
    let k : Fin 3 := ⟨j.val, h⟩
    quotientCoordinate (baseRepresentative k x) (D (B (tautFrame D x)) k)
  else if j = 3 then
    formComponent α (tautFrame D x) (baseFrame D x) (baseFrame D x)
  else
    formComponent β (tautFrame D x) (baseFrame D x)
      (fun k => frameResidual (baseFrame D x) (B (baseFrame D x k)))

private theorem smooth_linear [FiniteDimensional ℂ W] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (A : W →ₗ[ℂ] V) {u : Coordinates 10 → W} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x => A (u x)) :=
  (A.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hu

private theorem smooth_quotientCoordinate {v w : Coordinates 10 → Fin 2 → ℂ}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => quotientCoordinate (v x) (w x)) := by
  have h (i : Fin 2) := contDiff_apply ℝ (fun _ : Fin 2 => ℂ) (n := ∞) i
  exact ((h 0 |>.comp hv).mul (h 1 |>.comp hw)).sub
    ((h 1 |>.comp hv).mul (h 0 |>.comp hw))

private theorem smooth_formComponent [FiniteDimensional ℂ W] (a : LinearMap.BilinForm ℂ W)
    {X : Coordinates 10 → W} {u w : Coordinates 10 → Fin 3 → W}
    (hX : ContDiff ℝ ∞ X) (hu : ∀ i, ContDiff ℝ ∞ (fun x => u x i))
    (hw : ∀ i, ContDiff ℝ ∞ (fun x => w x i)) :
    ContDiff ℝ ∞ (fun x => formComponent a (X x) (u x) (w x)) := by
  have hinner (i : Fin 3) := hX.inner ℂ (hu i)
  have hb (i j : Fin 3) : ContDiff ℝ ∞ (fun x => a (w x i) (w x j)) :=
    (a.toContinuousBilinearMap.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂
      (hw i) (hw j)
  exact (((hinner 0).mul (hb 1 2)).sub ((hinner 1).mul (hb 0 2))).add
    ((hinner 2).mul (hb 0 1))

private theorem smooth_sectionCoordinates [FiniteDimensional ℂ W] (j : Fin 5) :
    ContDiff ℝ ∞ (sectionCoordinates D B α β j) := by
  change ContDiff ℝ ∞ (fun x => sectionCoordinates D B α β j x)
  by_cases hj : j.val < 3
  · let k : Fin 3 := ⟨j.val, hj⟩
    have hDB : ContDiff ℝ ∞ (fun x => D (B (tautFrame D x))) :=
      smooth_linear (D.toLinearMap.comp B) (smooth_tautFrame D)
    have hw : ContDiff ℝ ∞ (fun x => D (B (tautFrame D x)) k) :=
      (contDiff_apply ℝ (fun _ : Fin 3 => Fin 2 → ℂ) k).comp hDB
    simp only [sectionCoordinates, dite_eq_left hj]
    exact smooth_quotientCoordinate (smooth_baseRepresentative k) hw
  by_cases h3 : j = 3
  · simpa only [sectionCoordinates, dite_eq_right hj, ite_eq_left h3] using
      smooth_formComponent α (smooth_tautFrame D) (smooth_baseFrame D) (smooth_baseFrame D)
  · simpa only [sectionCoordinates, dite_eq_right hj, ite_eq_right h3] using
      smooth_formComponent β (smooth_tautFrame D) (smooth_baseFrame D)
        (fun k => smooth_frameResidual (smooth_baseFrame D) (linearIndependent_baseFrame D)
          (smooth_linear B (smooth_baseFrame D k)))

private theorem residual_equivariant [FiniteDimensional ℂ W]
    (i : Fin 10) (hi : i ∉ projectiveBox.periodic) (side : Bool) (x : Coordinates 10)
    (hx : x i = projectiveBox.face i side) (s : ℝ) (k : Fin 3) :
    let y := x + s • projectiveBox.tangent i side
    frameResidual (baseFrame D y) (B (baseFrame D y k)) =
      phase (s * baseCharge k i side) • frameResidual (baseFrame D x) (B (baseFrame D x k)) := by
  let y := x + s • projectiveBox.tangent i side
  have he (k : Fin 3) :
      baseFrame D y k = phase (s * baseCharge k i side) • baseFrame D x k :=
    baseFrame_equivariant D i hi side k x hx s
  have hs : span ℂ (Set.range (baseFrame D y)) = span ℂ (Set.range (baseFrame D x)) := by
    simp only [Submodule.span_range_eq_iSup]
    exact iSup_congr fun k => by
      rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (phase_ne_zero _))]
  change frameResidual (baseFrame D y) (B (baseFrame D y k)) = _
  rw [frameResidual_eq_projection (linearIndependent_baseFrame D y),
    frameResidual_eq_projection (linearIndependent_baseFrame D x), hs, he k, map_smul, map_smul]

private theorem quotientCoordinate_smul (v w : Fin 2 → ℂ) (a b : ℂ) :
    quotientCoordinate (a • v) (b • w) = (b * a) * quotientCoordinate v w := by
  simp only [quotientCoordinate, Pi.smul_apply, smul_eq_mul]
  ring

private theorem formComponent_phase (a : LinearMap.BilinForm ℂ W) (X : W) (u w : Fin 3 → W)
    (s t : ℝ) (q : Fin 3 → ℝ) :
    formComponent a (phase (s * t) • X) (fun k => phase (s * q k) • u k)
      (fun k => phase (s * q k) • w k) =
        phase (s * (q 0 + q 1 + q 2 - t)) * formComponent a X u w := by
  rw [formComponent_smul, star_phase, ← phase_add, ← phase_add, ← phase_add]
  congr 2
  ring

private theorem sectionCoordinates_equivariant [FiniteDimensional ℂ W]
    (i : Fin 10) (hi : i ∉ projectiveBox.periodic) (side : Bool) (j : Fin 5)
    (x : Coordinates 10) (hx : x i = projectiveBox.face i side) (s : ℝ) :
    sectionCoordinates D B α β j (x + s • projectiveBox.tangent i side) =
      phase (s * selectionCharge j i side) * sectionCoordinates D B α β j x := by
  have ht := tautFrame_equivariant D i hi side x hx s
  have hu : baseFrame D (x + s • projectiveBox.tangent i side) =
      fun k => phase (s * baseCharge k i side) • baseFrame D x k :=
    funext fun k => baseFrame_equivariant D i hi side k x hx s
  have hw : (fun k => frameResidual (baseFrame D (x + s • projectiveBox.tangent i side))
        (B (baseFrame D (x + s • projectiveBox.tangent i side) k))) =
      fun k => phase (s * baseCharge k i side) • frameResidual (baseFrame D x) (B (baseFrame D x k)) :=
    funext fun k => residual_equivariant D B i hi side x hx s k
  by_cases hj : j.val < 3
  · simp only [sectionCoordinates, selectionCharge, dite_eq_left hj, ht,
      baseRepresentative_equivariant i hi side _ x hx, map_smul, Pi.smul_apply]
    rw [quotientCoordinate_smul, ← phase_add, mul_add]
  by_cases h3 : j = 3
  · simp only [sectionCoordinates, selectionCharge, dite_eq_right hj, ite_eq_left h3, ht, hu]
    exact formComponent_phase α _ _ _ s _ _
  · simp only [sectionCoordinates, selectionCharge, dite_eq_right hj, ite_eq_right h3]
    rw [ht, hw, hu]
    exact formComponent_phase β _ _ _ s _ _

theorem sectionCoordinates_phaseSection [FiniteDimensional ℂ W] :
    PhaseSection projectiveBox selectionCharge (sectionCoordinates D B α β) := by
  refine ⟨smooth_sectionCoordinates D B α β, ?_, sectionCoordinates_equivariant D B α β⟩
  intro i hi j x
  simp only [sectionCoordinates, baseRepresentative_periodic i hi, tautFrame_periodic D i hi,
    baseFrame_periodic D i hi]

end SymmetricMaximizer.Geometry
