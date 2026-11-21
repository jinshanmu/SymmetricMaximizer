module

public import SymmetricMaximizer.Boundary
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Phase and the angular differential

The angular differential of a nonzero complex function is closed.
Its evaluation on a phase orbit gives the weight of that orbit.
-/

@[expose] public section

open scoped BigOperators ContDiff Topology

namespace SymmetricMaximizer.Geometry

variable {n : ℕ}

/-- The unit complex number of the given angle in radians. -/
noncomputable def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp [phase, add_mul, Complex.exp_add]

@[simp] theorem phase_ne_zero (t : ℝ) : phase t ≠ 0 := Complex.exp_ne_zero _

theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by simp [phase, Complex.norm_exp_mul_I]

theorem phase_mul_conj (t : ℝ) : phase t * star (phase t) = 1 := by
  rw [show star (phase t) = (starRingEnd ℂ) (phase t) from rfl, Complex.mul_conj', norm_phase]
  norm_num

theorem star_phase (t : ℝ) : star (phase t) = phase (-t) := by
  apply mul_left_cancel₀ (phase_ne_zero t)
  rw [phase_mul_conj, ← phase_add, add_neg_cancel, phase_zero]

theorem phase_periodic : Function.Periodic phase (2 * Real.pi) := by
  intro t
  unfold phase
  rw [Complex.ofReal_add, Complex.ofReal_mul]
  exact Complex.exp_mul_I_periodic (t : ℂ)

theorem smooth_phase : ContDiff ℝ ∞ phase :=
  (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

theorem hasDerivAt_phase_weight (q : ℝ) :
    HasDerivAt (fun s : ℝ => phase (s * q)) ((q : ℂ) * Complex.I) 0 := by
  have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id' 0)
  have hp := (hr.mul_const ((q : ℂ) * Complex.I)).cexp
  convert hp using 1
  · funext s
    simp [phase, mul_assoc]
  · simp

theorem phase_rotates_derivative {f : Coordinates n → ℂ} {x v : Coordinates n}
    (hf : DifferentiableAt ℝ f x) (q : ℝ)
    (h : ∀ s, f (x + s • v) = phase (s * q) * f x) :
    directional v f x = ((q : ℂ) * Complex.I) * f x := by
  rw [← (directional_on_line hf).deriv, funext h]
  exact ((hasDerivAt_phase_weight q).mul_const (f x)).deriv

/-- The real numerator of the angular differential of a complex-valued function. -/
noncomputable def angularNumerator (f : Coordinates n → ℂ) (x : Coordinates n) : Exterior n :=
  (f x).re • scalarD (fun y => (f y).im) x -
    (f x).im • scalarD (fun y => (f y).re) x

theorem smooth_realPart {f : Coordinates n → ℂ} (h : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => (f x).re) := Complex.reCLM.contDiff.comp h

theorem smooth_imagPart {f : Coordinates n → ℂ} (h : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => (f x).im) := Complex.imCLM.contDiff.comp h

private theorem differentiableAt_realPart {f : Coordinates n → ℂ} {x : Coordinates n}
    (h : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => (f y).re) x := Complex.reCLM.differentiableAt.comp x h

private theorem differentiableAt_imagPart {f : Coordinates n → ℂ} {x : Coordinates n}
    (h : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => (f y).im) x := Complex.imCLM.differentiableAt.comp x h

private theorem directional_realPart {f : Coordinates n → ℂ} {x v : Coordinates n}
    (h : DifferentiableAt ℝ f x) :
    directional v (fun y => (f y).re) x = (directional v f x).re :=
  directional_linear h Complex.reCLM

private theorem directional_imagPart {f : Coordinates n → ℂ} {x v : Coordinates n}
    (h : DifferentiableAt ℝ f x) :
    directional v (fun y => (f y).im) x = (directional v f x).im :=
  directional_linear h Complex.imCLM

theorem smooth_angularNumerator {f : Coordinates n → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (angularNumerator f) := by
  have hr := smooth_realPart hf
  have hi := smooth_imagPart hf
  exact (hr.smul (smooth_scalarD hi)).sub (hi.smul (smooth_scalarD hr))

theorem parity_angularNumerator (f : Coordinates n → ℂ) (x : Coordinates n) :
    parity (angularNumerator f x) = -angularNumerator f x := by
  simp only [angularNumerator, map_sub, map_smul, parity_scalarD, smul_neg, neg_sub]
  abel

theorem angularNumerator_eq_oneForm {f : Coordinates n → ℂ} {x : Coordinates n}
    (hf : DifferentiableAt ℝ f x) :
    angularNumerator f x = oneForm (fun i => (star (f x) * directional (axis i) f x).im) := by
  unfold angularNumerator scalarD
  rw [← map_smul, ← map_smul, ← map_sub]
  apply congrArg (fun u : Coordinates n => oneForm u)
  funext i
  rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    directional_realPart hf, directional_imagPart hf]
  simp [Complex.mul_im]
  ring

theorem contract_angularNumerator {f : Coordinates n → ℂ} {v x : Coordinates n}
    (hf : DifferentiableAt ℝ f x) :
    contract v (angularNumerator f x) =
      (star (f x) * directional v f x).im • (1 : Exterior n) := by
  rw [angularNumerator, map_sub, map_smul, map_smul, contract_scalarD, contract_scalarD,
    directional_imagPart hf, directional_realPart hf]
  rw [smul_smul, smul_smul, ← sub_smul]
  congr 1
  simp [Complex.mul_im]
  ring

theorem contract_angularNumerator_orbit {f : Coordinates n → ℂ} {v x : Coordinates n}
    (hf : DifferentiableAt ℝ f x) (q : ℝ)
    (h : ∀ s, f (x + s • v) = phase (s * q) * f x) :
    contract v (angularNumerator f x) = (Complex.normSq (f x) * q) • (1 : Exterior n) := by
  rw [contract_angularNumerator hf, phase_rotates_derivative hf q h]
  congr 1
  rw [show star (f x) * (((q : ℂ) * Complex.I) * f x) =
      (star (f x) * f x) * ((q : ℂ) * Complex.I) by ring]
  rw [show star (f x) * f x = (Complex.normSq (f x) : ℂ) by
    change (starRingEnd ℂ) (f x) * f x = _
    rw [mul_comm, Complex.mul_conj]]
  simp [Complex.mul_im]

private theorem covector_normal_eq {i : Fin n} {u w : Coordinates n}
    (h : ∀ j, j ≠ i → u j = w j) : dx i * oneForm u = dx i * oneForm w := by
  have he : u - w = (u i - w i) • axis i := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Pi.sub_apply, Pi.smul_apply]
    · simp [Pi.sub_apply, Pi.smul_apply, h j hji, Ne.symm hji]
  have hz : dx i * oneForm (u - w) = 0 := by
    rw [he, map_smul, mul_smul_comm, ← dx, dx_sq, smul_zero]
  rwa [map_sub, mul_sub, sub_eq_zero] at hz

theorem angularNumerator_face_invariant {f : Coordinates n → ℂ}
    (hf : Differentiable ℝ f) {i : Fin n} {x v : Coordinates n} {c q : ℝ}
    (hx : x i = c)
    (h : ∀ y, y i = c → ∀ s : ℝ, f (y + s • v) = phase (s * q) * f y)
    (s : ℝ) :
    dx i * angularNumerator f (x + s • v) = dx i * angularNumerator f x := by
  rw [angularNumerator_eq_oneForm (hf _), angularNumerator_eq_oneForm (hf _)]
  apply covector_normal_eq
  intro j hji
  let z := phase (s * q)
  let M := (LinearMap.mul ℝ ℂ z).toContinuousLinearMap
  have hs : ∀ r : ℝ, f ((x + s • v) + r • axis j) = M (f (x + r • axis j)) := by
    intro r
    rw [show (x + s • v) + r • axis j = (x + r • axis j) + s • v by abel,
      h _ (on_face_add_smul hx (by simp [hji]) r)]
    rfl
  have hd := directional_eq_of_line_eq (hf _) (M.differentiableAt.comp x (hf x)) hs
  change directional (axis j) f (x + s • v) =
    directional (axis j) (fun y => M (f y)) x at hd
  rw [directional_linear (hf x) M] at hd
  have hd' : directional (axis j) f (x + s • v) = z * directional (axis j) f x := hd
  rw [h x hx s, hd']
  change (star (z * f x) * (z * directional (axis j) f x)).im = _
  rw [star_mul]
  rw [show (star (f x) * star z) * (z * directional (axis j) f x) =
      z * star z * (star (f x) * directional (axis j) f x) by ring, phase_mul_conj, one_mul]

theorem angularNumerator_periodic {f : Coordinates n → ℂ} (hf : Differentiable ℝ f)
    {p : Coordinates n} (hp : ∀ x, f (x + p) = f x) (x : Coordinates n) :
    angularNumerator f (x + p) = angularNumerator f x := by
  rw [angularNumerator_eq_oneForm (hf _), angularNumerator_eq_oneForm (hf _)]
  simp only [hp, directional_periodic hf hp]

private theorem scalarD_add {f g : Coordinates n → ℝ} {x : Coordinates n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    scalarD (fun y => f y + g y) x = scalarD f x + scalarD g x := by
  simp only [scalarD, directional, fderiv_fun_add hf hg, add_apply, ← map_add]
  rfl

private theorem scalarD_mul {f g : Coordinates n → ℝ} {x : Coordinates n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    scalarD (fun y => f y * g y) x = f x • scalarD g x + g x • scalarD f x := by
  simp only [scalarD, directional, fderiv_fun_mul hf hg, add_apply, smul_apply]
  rw [← map_smul, ← map_smul, ← map_add]
  apply congrArg (fun w : Coordinates n => oneForm w)
  funext i
  rfl

private theorem scalarD_inv {f : Coordinates n → ℝ} {x : Coordinates n}
    (hf : DifferentiableAt ℝ f x) (hn : f x ≠ 0) :
    scalarD (fun y => (f y)⁻¹) x = (-(f x)⁻¹ ^ 2) • scalarD f x := by
  unfold scalarD
  rw [← map_smul]
  apply congrArg (fun w : Coordinates n => oneForm w)
  funext i
  have hs := directional_on_line (v := axis i) hf
  have hi := directional_on_line (F := fun y => (f y)⁻¹) (v := axis i) (hf.inv hn)
  have hh : f (x + (0 : ℝ) • axis i) ≠ 0 := by simpa using hn
  have hh' := (HasDerivAt.inv hs hh).deriv
  change deriv (fun t : ℝ => (f (x + t • axis i))⁻¹) 0 = _ at hh'
  rw [hi.deriv] at hh'
  rw [Pi.smul_apply, smul_eq_mul, hh']
  simp only [zero_smul, add_zero]
  field_simp

private theorem scalarD_normSq {f : Coordinates n → ℂ} {x : Coordinates n}
    (h : DifferentiableAt ℝ f x) :
    scalarD (fun y => Complex.normSq (f y)) x =
      (2 * (f x).re) • scalarD (fun y => (f y).re) x +
        (2 * (f x).im) • scalarD (fun y => (f y).im) x := by
  have hr := differentiableAt_realPart h
  have hi := differentiableAt_imagPart h
  have hr₂ : DifferentiableAt ℝ (fun y => (f y).re * (f y).re) x := hr.mul hr
  have hi₂ : DifferentiableAt ℝ (fun y => (f y).im * (f y).im) x := hi.mul hi
  simp only [Complex.normSq_apply]
  rw [scalarD_add hr₂ hi₂, scalarD_mul hr hr, scalarD_mul hi hi]
  module

theorem smooth_normSq_comp {f : Coordinates n → ℂ} (h : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => Complex.normSq (f y)) := by
  simp only [Complex.normSq_apply]
  have hr := smooth_realPart h
  have hi := smooth_imagPart h
  exact (hr.mul hr).add (hi.mul hi)

theorem exteriorD_angular {f : Coordinates n → ℂ} (hf : ContDiff ℝ ∞ f)
    {x : Coordinates n} (h₀ : f x ≠ 0) :
    exteriorD (fun y => (Complex.normSq (f y))⁻¹ • angularNumerator f y) x = 0 := by
  have hfd := hf.differentiable (by simp) x
  have hrSmooth := smooth_realPart hf
  have hiSmooth := smooth_imagPart hf
  have hre := hrSmooth.differentiable (by simp) x
  have him := hiSmooth.differentiable (by simp) x
  let r := Complex.normSq (f x)
  let u := (f x).re
  let v := (f x).im
  let du := scalarD (fun y => (f y).re) x
  let dv := scalarD (fun y => (f y).im) x
  have hr : r ≠ 0 := mt Complex.normSq_eq_zero.mp h₀
  have hr' : r = u * u + v * v := Complex.normSq_apply _
  have hA : angularNumerator f x = u • dv - v • du := rfl
  have hdu : du * du = 0 := ExteriorAlgebra.ι_sq_zero _
  have hdv : dv * dv = 0 := ExteriorAlgebra.ι_sq_zero _
  have hs : dv * du = -(du * dv) := oneForm_anticomm _ _
  have hD : exteriorD (angularNumerator f) x = (2 : ℝ) • (du * dv) := by
    unfold angularNumerator
    have hF : DifferentiableAt ℝ (fun y => (f y).re • scalarD (fun z => (f z).im) y) x :=
      hre.smul ((smooth_scalarD hiSmooth).differentiable (by simp) x)
    have hG : DifferentiableAt ℝ (fun y => (f y).im • scalarD (fun z => (f z).re) y) x :=
      him.smul ((smooth_scalarD hrSmooth).differentiable (by simp) x)
    rw [exteriorD_sub hF hG,
      exteriorD_smul hre ((smooth_scalarD hiSmooth).differentiable (by simp) x),
      exteriorD_smul him ((smooth_scalarD hrSmooth).differentiable (by simp) x),
      exteriorD_scalarD hrSmooth, exteriorD_scalarD hiSmooth]
    change du * dv + u • 0 - (dv * du + v • 0) = _
    rw [smul_zero, smul_zero, add_zero, add_zero, hs, sub_neg_eq_add, two_smul]
  have hR := (smooth_normSq_comp hf).differentiable (by simp) x
  have hinv : DifferentiableAt ℝ (fun y => (Complex.normSq (f y))⁻¹) x := hR.inv hr
  rw [exteriorD_smul hinv ((smooth_angularNumerator hf).differentiable (by simp) x),
    scalarD_inv hR hr, scalarD_normSq hfd, hA, hD]
  change (-(r⁻¹ ^ 2)) • ((2 * u) • du + (2 * v) • dv) * (u • dv - v • du) +
    r⁻¹ • ((2 : ℝ) • (du * dv)) = 0
  rw [smul_mul_assoc]
  have hp : ((2 * u) • du + (2 * v) • dv) * (u • dv - v • du) = (2 * r) • (du * dv) := by
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hdu, hdv, hs,
      smul_zero, smul_neg]
    rw [hr']
    module
  rw [hp, smul_smul, smul_smul, ← add_smul]
  have hc : -(r⁻¹ ^ 2) * (2 * r) + r⁻¹ * 2 = 0 := by
    field_simp
    ring
  rw [hc, zero_smul]

end SymmetricMaximizer.Geometry
