module

public import SymmetricMaximizer.ExteriorCalculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-!
# Contraction and Cartan's identity

Contraction detects which differential forms vanish on the collapsing
directions of a projective coordinate face.
-/

@[expose] public section

open Finset Module
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

variable {n : ℕ}

/-- Evaluation of a coordinate covector on a coordinate vector. -/
noncomputable def evaluateOn (v : Coordinates n) : Module.Dual ℝ (Coordinates n) where
  toFun u := ∑ i, v i * u i
  map_add' u w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

@[simp] theorem evaluateOn_axis (v : Coordinates n) (i : Fin n) : evaluateOn v (axis i) = v i := by
  classical
  simp [evaluateOn, mul_ite]

/-- Interior multiplication by a constant coordinate vector. -/
noncomputable def contract (v : Coordinates n) : Exterior n →L[ℝ] Exterior n :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Coordinates n)))
    (evaluateOn v)).toContinuousLinearMap

@[simp] theorem contract_oneForm (v u : Coordinates n) :
    contract v (oneForm u) = evaluateOn v u • (1 : Exterior n) := by
  change CliffordAlgebra.contractLeft (evaluateOn v) (CliffordAlgebra.ι _ u) = _
  rw [CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one]

@[simp] theorem contract_dx (v : Coordinates n) (i : Fin n) :
    contract v (dx i) = v i • (1 : Exterior n) := by
  rw [dx, contract_oneForm, evaluateOn_axis]

@[simp] theorem contract_one (v : Coordinates n) : contract v (1 : Exterior n) = 0 :=
  CliffordAlgebra.contractLeft_one 0 (evaluateOn v)

theorem contract_oneForm_mul (v u : Coordinates n) (a : Exterior n) :
    contract v (oneForm u * a) = evaluateOn v u • a - oneForm u * contract v a :=
  CliffordAlgebra.contractLeft_ι_mul (evaluateOn v) u a

/-- Contraction is a graded derivation. -/
theorem contract_mul (v : Coordinates n) (a b : Exterior n) :
    contract v (a * b) = contract v a * b + parity a * contract v b := by
  induction a using ExteriorAlgebra.induction generalizing b with
  | algebraMap r =>
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, contract_one,
      smul_zero, zero_mul, zero_add, map_one]
  | ι u =>
    rw [contract_oneForm_mul, contract_oneForm, parity_oneForm, smul_mul_assoc, one_mul, neg_mul,
      sub_eq_add_neg]
  | mul a b ha hb =>
    rw [mul_assoc, ha, hb, ← mul_assoc, ha, map_mul, mul_add, add_mul, mul_assoc, add_assoc, mul_assoc]
    simp only [mul_assoc]
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    abel

/-- Cartan's identity for a constant vector in rectangular coordinates. -/
theorem contract_exteriorD (v : Coordinates n) {F : Coordinates n → Exterior n}
    {x : Coordinates n} (hF : DifferentiableAt ℝ F x) :
    contract v (exteriorD F x) =
      directional v F x - exteriorD (fun y => contract v (F y)) x := by
  simp only [exteriorD, map_sum, dx, contract_oneForm_mul, evaluateOn_axis,
    directional_linear hF, Finset.sum_sub_distrib]
  congr 1
  change ∑ i, v i • fderiv ℝ F x (axis i) = fderiv ℝ F x v
  rw [← sum_axis v, map_sum]
  simp only [map_smul, sum_axis]

theorem parity_exteriorD {F : Coordinates n → Exterior n} {x : Coordinates n}
    (hF : DifferentiableAt ℝ F x) :
    parity (exteriorD F x) = -exteriorD (fun y => parity (F y)) x := by
  simp only [exteriorD, map_sum, map_mul, dx, parity_oneForm, neg_mul, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (oneForm (axis i) * ·)
    (directional_linear hF parity.toLinearMap.toContinuousLinearMap).symm

theorem exteriorD_neg {F : Coordinates n → Exterior n} {x : Coordinates n} :
    exteriorD (fun y => -F y) x = -exteriorD F x := by
  simp [exteriorD, directional, fderiv_fun_neg, mul_neg, Finset.sum_neg_distrib]

/-- The exterior derivative of an odd form has even degree parity. -/
theorem parity_exteriorD_of_odd {F : Coordinates n → Exterior n} {x : Coordinates n}
    (hF : DifferentiableAt ℝ F x) (hodd : ∀ y, parity (F y) = -F y) :
    parity (exteriorD F x) = exteriorD F x := by
  rw [parity_exteriorD hF, show (fun y => parity (F y)) = (fun y => -F y) from funext hodd,
    exteriorD_neg, neg_neg]

/-- The covector of the differential of a scalar function. -/
noncomputable def scalarD (f : Coordinates n → ℝ) (x : Coordinates n) : Exterior n :=
  oneForm (fun i => directional (axis i) f x)

theorem scalarD_eq_sum (f : Coordinates n → ℝ) (x : Coordinates n) :
    scalarD f x = ∑ i, directional (axis i) f x • dx i := by
  unfold scalarD dx
  conv_lhs => rw [← sum_axis (fun i => directional (axis i) f x), map_sum]
  simp only [map_smul]

theorem smooth_scalarD {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarD f) :=
  oneForm.toContinuousLinearMap.contDiff.comp
    (contDiff_pi.mpr fun i => smooth_directional hf (axis i))

@[simp] theorem parity_scalarD (f : Coordinates n → ℝ) (x : Coordinates n) :
    parity (scalarD f x) = -scalarD f x :=
  parity_oneForm _

theorem contract_scalarD (v : Coordinates n) (f : Coordinates n → ℝ) (x : Coordinates n) :
    contract v (scalarD f x) = directional v f x • (1 : Exterior n) := by
  rw [scalarD, contract_oneForm]
  congr 1
  change ∑ i, v i * fderiv ℝ f x (axis i) = fderiv ℝ f x v
  conv_rhs => rw [← sum_axis v, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem exteriorD_smul {f : Coordinates n → ℝ} {F : Coordinates n → Exterior n}
    {x : Coordinates n} (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F x) :
    exteriorD (fun y => f y • F y) x = scalarD f x * F x + f x • exteriorD F x := by
  simp only [scalarD_eq_sum, exteriorD, directional, fderiv_fun_smul hf hF,
    add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.smul_sum]
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, smul_mul_assoc]
  · exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _

theorem exteriorD_const (a : Exterior n) (x : Coordinates n) :
    exteriorD (fun _ => a) x = 0 := by simp [exteriorD, directional]

theorem scalarD_eq_exteriorD {f : Coordinates n → ℝ} {x : Coordinates n}
    (hf : DifferentiableAt ℝ f x) :
    scalarD f x = exteriorD (fun y => f y • (1 : Exterior n)) x := by
  rw [exteriorD_smul hf (differentiableAt_const _), exteriorD_const, mul_one, smul_zero, add_zero]

theorem exteriorD_scalarD {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (x : Coordinates n) :
    exteriorD (scalarD f) x = 0 := by
  have hfun : scalarD f = fun x => exteriorD (fun y => f y • (1 : Exterior n)) x :=
    funext fun y => scalarD_eq_exteriorD (hf.differentiable (by simp) y)
  rw [hfun]
  exact exteriorD_sq (hf.smul contDiff_const) x

end SymmetricMaximizer.Geometry
