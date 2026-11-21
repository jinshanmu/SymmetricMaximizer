module

public import SymmetricMaximizer.ProjectiveConnections
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Fiber integration in polar coordinates

For the two fiber polar pairs put `s = sin² b₀` and `q = sin² b₁`.
The normalized fiber measure has density `2s ds dq`.
The coefficient of the three base area forms and the fiber volume
therefore reduces to elementary one-dimensional integrals.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Interval

namespace SymmetricMaximizer.Geometry

/-- Squared radius coordinate on an amplitude interval. -/
noncomputable def polarSquare (t : ℝ) : ℝ := Real.sin t ^ 2

/-- Derivative of the squared radius coordinate. -/
noncomputable def polarRate (t : ℝ) : ℝ := 2 * Real.sin t * Real.cos t

private theorem hasDerivAt_polarSquare (t : ℝ) : HasDerivAt polarSquare (polarRate t) t := by
  have h := (Real.hasDerivAt_sin t).pow 2
  change HasDerivAt (fun y => Real.sin y ^ 2) _ t at h
  unfold polarSquare polarRate
  simpa only [Nat.reduceSub, Nat.cast_ofNat, pow_one] using h

private theorem continuous_polarSquare : Continuous polarSquare := by unfold polarSquare; fun_prop

private theorem continuous_polarRate : Continuous polarRate := by unfold polarRate; fun_prop

private theorem polarIntegral_derivative {f g : ℝ → ℝ} (hg : Continuous g)
    (hf : ∀ t, HasDerivAt f (g t) t) :
    (∫ t in Icc 0 (Real.pi / 2), g t) = f (Real.pi / 2) - f 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t)
    (hg.intervalIntegrable _ _)

private theorem integral_polarRate : (∫ t in Icc 0 (Real.pi / 2), polarRate t) = 1 := by
  rw [polarIntegral_derivative continuous_polarRate hasDerivAt_polarSquare]
  norm_num [polarSquare]

private theorem integral_phase_one : (∫ _t in Icc 0 (2 * Real.pi), (1 : ℝ)) = 2 * Real.pi := by
  rw [setIntegral_const, measureReal_def, Real.volume_Icc]
  simp [Real.pi_pos.le]

private theorem integral_box_product {n : ℕ} (a b : Coordinates n) (f : Fin n → ℝ → ℝ) :
    (∫ x in Icc a b, ∏ i, f i (x i)) = ∏ i, ∫ t in Icc (a i) (b i), f i t := by
  rw [← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod f

private noncomputable def polarProduct (f g : ℝ → ℝ) (x : Coordinates 10) : ℝ :=
  polarRate (x 0) * polarRate (x 2) * polarRate (x 4) * f (x 6) * g (x 8)

private theorem integral_polarProduct (f g : ℝ → ℝ) :
    (∫ x in Icc projectiveBox.lower projectiveBox.upper, polarProduct f g x) =
      (2 * Real.pi) ^ 5 * (∫ t in Icc 0 (Real.pi / 2), f t) *
        (∫ t in Icc 0 (Real.pi / 2), g t) := by
  let u : Fin 10 → ℝ → ℝ :=
    ![polarRate, fun _ => 1, polarRate, fun _ => 1, polarRate, fun _ => 1,
      f, fun _ => 1, g, fun _ => 1]
  have he (x : Coordinates 10) : polarProduct f g x = ∏ i, u i (x i) := by
    norm_num [polarProduct, u, Fin.prod_univ_succ, mul_assoc]
  simp_rw [he]
  rw [integral_box_product]
  norm_num [u, projectiveBox, Fin.prod_univ_succ, integral_polarRate, integral_phase_one]
  rw [max_eq_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
  ring

/-- Oriented density for the product of the base volume and the square of the fiber curvature. -/
noncomputable def polarVolumeDensity (x : Coordinates 10) : ℝ :=
  (polarAreaDeriv 0 x * polarAreaDeriv 1 x * polarAreaDeriv 2 x) *
    (2 * (polarAreaDeriv 3 x * (polarArea 3 x * polarAreaDeriv 4 x)))

/-- The base volume and the fiber curvature square each integrate to one after normalization
by their phase periods. -/
theorem integral_polarVolumeDensity :
    (∫ x in Icc projectiveBox.lower projectiveBox.upper, polarVolumeDensity x) =
      (2 * Real.pi) ^ 5 := by
  let fiberAmplitude : ℝ → ℝ := fun t => 2 * polarSquare t * polarRate t
  have hDensity (x : Coordinates 10) :
      polarVolumeDensity x = polarProduct fiberAmplitude polarRate x := by
    change polarRate (x 0) * polarRate (x 2) * polarRate (x 4) *
      (2 * (polarRate (x 6) * (polarSquare (x 6) * polarRate (x 8)))) =
        polarRate (x 0) * polarRate (x 2) * polarRate (x 4) *
          (2 * polarSquare (x 6) * polarRate (x 6)) * polarRate (x 8)
    ring
  have hFiber : (∫ t in Icc 0 (Real.pi / 2), fiberAmplitude t) = 1 := by
    rw [polarIntegral_derivative (f := fun t => polarSquare t ^ 2)
      (by unfold fiberAmplitude polarSquare polarRate; fun_prop) ?_]
    · norm_num [polarSquare]
    · intro t
      convert (hasDerivAt_polarSquare t).pow 2 using 1
      simp [fiberAmplitude]
  simp_rw [hDensity]
  rw [integral_polarProduct, hFiber, integral_polarRate, mul_one, mul_one]

end SymmetricMaximizer.Geometry
