module

public import SymmetricMaximizer.ProjectiveBox
public import SymmetricMaximizer.MovingProjection
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Tactic

/-!
# Frames over the polar box

A basis in each summand identifies the algebraic direct sum with three
two-coordinate blocks. The polar representatives select one vector in each
block and a vector on the tautological line in their span.
-/

@[expose] public section

open Module Submodule Finset
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- Coordinates adapted to the algebraic direct sum of the three two-planes. -/
noncomputable def blockCoordinates (E : Fin 3 → Submodule ℂ W)
    (hindep : iSupIndep E) (htop : (⨆ i, E i) = ⊤)
    (basis : ∀ i, Basis (Fin 2) ℂ (E i)) : W ≃ₗ[ℂ] (Fin 3 → Fin 2 → ℂ) :=
  ((hindep.linearEquiv htop).symm.trans DFinsupp.linearEquivFunOnFintype).trans
    (LinearEquiv.piCongrRight fun i => (basis i).equivFun)

theorem blockCoordinates_apply_submodule (E : Fin 3 → Submodule ℂ W)
    (hindep : iSupIndep E) (htop : (⨆ i, E i) = ⊤)
    (basis : ∀ i, Basis (Fin 2) ℂ (E i)) (i : Fin 3) (y : E i) :
    blockCoordinates E hindep htop basis (y : W) = Pi.single i ((basis i).equivFun y) := by
  ext j k
  change (basis j).equivFun ((hindep.linearEquiv htop).symm (y : W) j) k = _
  rw [hindep.linearEquiv_symm_apply htop y.property]
  by_cases h : j = i
  · subst j
    simp
  · simp [DFinsupp.single_eq_of_ne h, Pi.single_eq_of_ne h]

variable (D : W ≃ₗ[ℂ] (Fin 3 → Fin 2 → ℂ))

/-- The three polar representatives embedded in the ambient space. -/
noncomputable def baseFrame (x : Coordinates 10) (i : Fin 3) : W :=
  D.symm (Pi.single i (baseRepresentative i x))

/-- The ambient polar representative of the tautological line. -/
noncomputable def tautFrame (x : Coordinates 10) : W :=
  ∑ i, tautCoefficients x i • baseFrame D x i

theorem baseRepresentative_ne_zero (i : Fin 3) (x : Coordinates 10) :
    baseRepresentative i x ≠ 0 := by
  intro h
  simpa [h] using baseRepresentative_normSq i x

theorem baseFrame_ne_zero (x : Coordinates 10) (i : Fin 3) : baseFrame D x i ≠ 0 := by
  intro h
  have hz := congrArg (fun y : W => D y i) h
  apply baseRepresentative_ne_zero i x
  simpa [baseFrame] using hz

theorem blockCoordinates_baseFrame (E : Fin 3 → Submodule ℂ W)
    (hindep : iSupIndep E) (htop : (⨆ i, E i) = ⊤)
    (basis : ∀ i, Basis (Fin 2) ℂ (E i)) (x : Coordinates 10) (i : Fin 3) :
    baseFrame (blockCoordinates E hindep htop basis) x i ∈ E i := by
  let y := (basis i).equivFun.symm (baseRepresentative i x)
  have h := blockCoordinates_apply_submodule E hindep htop basis i y
  have he : baseFrame (blockCoordinates E hindep htop basis) x i = (y : W) := by
    apply (blockCoordinates E hindep htop basis).injective
    simpa only [baseFrame, y, LinearEquiv.apply_symm_apply] using h.symm
  rw [he]
  exact y.property

theorem coordinates_sum_frame (x : Coordinates 10) (a : Fin 3 → ℂ) (k : Fin 3) :
    D (∑ i, a i • baseFrame D x i) k = a k • baseRepresentative k x := by
  simp only [baseFrame, map_sum, map_smul, LinearEquiv.apply_symm_apply, Finset.sum_apply,
    Pi.smul_apply]
  exact Finset.sum_eq_single_of_mem k (mem_univ k)
    (fun i _ hi => by rw [Pi.single_eq_of_ne hi.symm, smul_zero]) |>.trans
      (by rw [Pi.single_eq_same])

theorem linearIndependent_baseFrame (x : Coordinates 10) : LinearIndependent ℂ (baseFrame D x) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hz : a i • baseRepresentative i x = 0 := by
    rw [← coordinates_sum_frame D x a i, ha, map_zero]
    rfl
  exact (smul_eq_zero.mp hz).resolve_right (baseRepresentative_ne_zero i x)

theorem tautFrame_ne_zero (x : Coordinates 10) : tautFrame D x ≠ 0 := by
  intro h
  have hz := Fintype.linearIndependent_iff.mp (linearIndependent_baseFrame D x) _ h
  simpa [hz] using tautCoefficients_normSq x

theorem tautFrame_mem_span (x : Coordinates 10) :
    tautFrame D x ∈ Submodule.span ℂ (Set.range (baseFrame D x)) :=
  (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨tautCoefficients x, rfl⟩

private theorem smooth_cos_coordinate (i : Fin 10) :
    ContDiff ℝ ∞ (fun x : Coordinates 10 => (Real.cos (x i) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp (contDiff_apply ℝ (fun _ => ℝ) i))

private theorem smooth_sin_coordinate (i : Fin 10) :
    ContDiff ℝ ∞ (fun x : Coordinates 10 => (Real.sin (x i) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ => ℝ) i))

private theorem smooth_phase_coordinate (i : Fin 10) :
    ContDiff ℝ ∞ (fun x : Coordinates 10 => phase (x i)) :=
  smooth_phase.comp (contDiff_apply ℝ (fun _ => ℝ) i)

theorem smooth_baseRepresentative (i : Fin 3) : ContDiff ℝ ∞ (baseRepresentative i) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases k
  · exact smooth_cos_coordinate _
  · exact (smooth_sin_coordinate _).mul (smooth_phase_coordinate _)

theorem smooth_tautCoefficient (k : Fin 3) :
    ContDiff ℝ ∞ (fun x => tautCoefficients x k) := by
  fin_cases k
  · exact smooth_cos_coordinate 6
  · change ContDiff ℝ ∞ (fun x : Coordinates 10 =>
      ((Real.sin (x 6) * Real.cos (x 8) : ℝ) : ℂ) * phase (x 7))
    simp only [Complex.ofReal_mul]
    exact ((smooth_sin_coordinate 6).mul (smooth_cos_coordinate 8)).mul (smooth_phase_coordinate 7)
  · change ContDiff ℝ ∞ (fun x : Coordinates 10 =>
      ((Real.sin (x 6) * Real.sin (x 8) : ℝ) : ℂ) * phase (x 9))
    simp only [Complex.ofReal_mul]
    exact ((smooth_sin_coordinate 6).mul (smooth_sin_coordinate 8)).mul (smooth_phase_coordinate 9)

theorem smooth_baseFrame (i : Fin 3) : ContDiff ℝ ∞ (fun x => baseFrame D x i) := by
  let A := D.symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ : Fin 3 => Fin 2 → ℂ) i
  exact (A.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (smooth_baseRepresentative i)

theorem smooth_tautFrame : ContDiff ℝ ∞ (tautFrame D) :=
  ContDiff.sum fun i _ => (smooth_tautCoefficient i).smul (smooth_baseFrame D i)

theorem baseFrame_periodic (i : Fin 10) (hi : i ∈ projectiveBox.periodic) (x : Coordinates 10) :
    baseFrame D (x + projectiveBox.period i) = baseFrame D x := by
  funext k
  rw [baseFrame, baseRepresentative_periodic i hi]
  rfl

theorem tautFrame_periodic (i : Fin 10) (hi : i ∈ projectiveBox.periodic) (x : Coordinates 10) :
    tautFrame D (x + projectiveBox.period i) = tautFrame D x := by
  simp only [tautFrame, tautCoefficients_periodic i hi, baseFrame_periodic D i hi]

theorem baseFrame_equivariant (i : Fin 10) (hi : i ∉ projectiveBox.periodic)
    (side : Bool) (k : Fin 3) (x : Coordinates 10) (hx : x i = projectiveBox.face i side)
    (s : ℝ) :
    baseFrame D (x + s • projectiveBox.tangent i side) k =
      phase (s * baseCharge k i side) • baseFrame D x k := by
  simp only [baseFrame, baseRepresentative_equivariant i hi side k x hx,
    Pi.single_smul, map_smul]

theorem tautFrame_equivariant (i : Fin 10) (hi : i ∉ projectiveBox.periodic)
    (side : Bool) (x : Coordinates 10) (hx : x i = projectiveBox.face i side) (s : ℝ) :
    tautFrame D (x + s • projectiveBox.tangent i side) =
      phase (s * tautCharge i side) • tautFrame D x := by
  unfold tautFrame
  rw [smul_sum]
  apply sum_congr rfl
  intro k _
  rw [tautCoefficients_equivariant i hi side k x hx, baseFrame_equivariant D i hi side k x hx,
    smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (tautCoefficients x k), ← mul_assoc, ← phase_add]
  congr 2
  ring

end SymmetricMaximizer.Geometry
