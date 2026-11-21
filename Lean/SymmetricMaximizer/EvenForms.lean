module

public import SymmetricMaximizer.ExteriorCalculus
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Tactic

/-!
# Products of exterior forms

Even forms commute with every form. A decomposable two-form has square
zero, as used for the base curvature and the two fiber area factors.
-/

@[expose] public section

namespace SymmetricMaximizer.Geometry

variable {n : ℕ}

theorem mem_center_of_even {z : Exterior n} (hz : parity z = z) :
    z ∈ Subalgebra.center ℝ (Exterior n) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using ExteriorAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r z
  | ι v => rw [oneForm_mul v z, hz]
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, ha, hb, mul_add]

theorem parity_two_covectors (v w : Coordinates n) :
    parity (oneForm v * oneForm w) = oneForm v * oneForm w := by simp

theorem two_covectors_sq (v w : Coordinates n) :
    (oneForm v * oneForm w) ^ 2 = 0 := by
  rw [pow_two]
  calc
    _ = oneForm v * ((oneForm w * oneForm v) * oneForm w) := by simp [mul_assoc]
    _ = -((oneForm v * oneForm v) * (oneForm w * oneForm w)) := by
      rw [oneForm_anticomm w v]
      noncomm_ring
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero]

end SymmetricMaximizer.Geometry
