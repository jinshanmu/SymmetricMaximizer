module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic

/-!
# Fiber integration in `lem:selection`

The ring and projection-formula calculation in the manuscript, with the geometric identities
stated as hypotheses on the base ring, the total-space ring, and fiber integration.
-/

public section

namespace SymmetricMaximizer

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The Chern polynomial reduces to `-4 h₁ h₂ h₃ t²` modulo the tautological relation.
The explicit multiple of the relation can be used before passing to cohomology. -/
theorem topChern_polynomial_reduce (a b c t : R)
    (ha : a ^ 2 = 0) (hb : b ^ 2 = 0) (hc : c ^ 2 = 0) :
    let h := a + b + c
    (h - t) ^ 2 * ((t + a) * (t + b) * (t + c)) =
      (t ^ 2 - h ^ 2) * ((t - a) * (t - b) * (t - c)) - 4 * (a * b * c) * t ^ 2 := by
  let h := a + b + c
  let e₂ := a * b + a * c + b * c
  let e₃ := a * b * c
  let r := (t - a) * (t - b) * (t - c)
  have he : h * e₂ = 3 * e₃ := by
    dsimp [h, e₂, e₃]
    linear_combination (b + c) * ha + (a + c) * hb + (a + b) * hc
  have hz : h * e₃ = 0 := by
    dsimp [h, e₃]
    linear_combination b * c * ha + a * c * hb + a * b * hc
  have cubic : t ^ 3 = h * t ^ 2 - e₂ * t + e₃ + r := by
    dsimp [r, h, e₂, e₃]
    ring
  have quartic : t ^ 4 = h * t ^ 3 - e₂ * t ^ 2 + e₃ * t + t * r := by
    linear_combination t * cubic
  have hplus : (t + a) * (t + b) * (t + c) = 2 * (h * t ^ 2 + e₃) + r := by
    dsimp [r, h, e₃]
    ring
  change (h - t) ^ 2 * _ = (t ^ 2 - h ^ 2) * r - 4 * e₃ * t ^ 2
  rw [hplus]
  linear_combination 2 * h * quartic - 2 * h ^ 2 * cubic +
    (2 * h * t - 2 * t ^ 2) * he + 4 * t * hz

/-- Pushing the top-Chern polynomial to the base gives `-4 h₁ h₂ h₃`. -/
theorem push_topChern_polynomial (h₁ h₂ h₃ : R) (t : S) (push : S →ₗ[R] R)
    (hh₁ : h₁ ^ 2 = 0) (hh₂ : h₂ ^ 2 = 0) (hh₃ : h₃ ^ 2 = 0)
    (hrel : (t - algebraMap R S h₁) * (t - algebraMap R S h₂) *
      (t - algebraMap R S h₃) = 0)
    (hzero : push 1 = 0) (hone : push t = 0) (htwo : push (t ^ 2) = 1) :
    push ((algebraMap R S (h₁ + h₂ + h₃) - t) ^ 2 *
      ((t + algebraMap R S h₁) * (t + algebraMap R S h₂) * (t + algebraMap R S h₃))) =
      -4 * (h₁ * h₂ * h₃) := by
  let h := h₁ + h₂ + h₃
  let e₂ := h₁ * h₂ + h₁ * h₃ + h₂ * h₃
  let e₃ := h₁ * h₂ * h₃
  let f := algebraMap R S
  have hs : h ^ 2 = 2 * e₂ := by
    dsimp [h, e₂]
    linear_combination hh₁ + hh₂ + hh₃
  have he : h * e₂ = 3 * e₃ := by
    dsimp [h, e₂, e₃]
    linear_combination (h₂ + h₃) * hh₁ + (h₁ + h₃) * hh₂ + (h₁ + h₂) * hh₃
  have projection (a : R) (z : S) : push (f a * z) = a * push z := by
    change push (algebraMap R S a * z) = a * push z
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have constant (a : R) : push (f a) = 0 := by
    rw [← mul_one (f a), projection, hzero, mul_zero]
  have cubic : t ^ 3 = f h * t ^ 2 - f e₂ * t + f e₃ := by
    dsimp only [f, h, e₂, e₃]
    simp only [map_add, map_mul]
    linear_combination hrel
  have quartic : t ^ 4 = f h * t ^ 3 - f e₂ * t ^ 2 + f e₃ * t := by
    linear_combination t * cubic
  have pushCubic : push (t ^ 3) = h := by
    rw [cubic, map_add, map_sub, projection, projection, constant, htwo, hone]
    ring
  have pushQuartic : push (t ^ 4) = e₂ := by
    rw [quartic, map_add, map_sub, projection, projection, projection, pushCubic, htwo, hone]
    linear_combination hs
  have prod : (t + f h₁) * (t + f h₂) * (t + f h₃) = 2 * (f h * t ^ 2 + f e₃) := by
    dsimp only [f, h, e₂, e₃] at cubic ⊢
    simp only [map_add, map_mul] at cubic ⊢
    linear_combination cubic
  have pushSquare : push ((f h - t) ^ 2) = 1 := by
    rw [show (f h - t) ^ 2 = f (h ^ 2) - f (2 * h) * t + t ^ 2 by
      simp only [map_pow, map_mul, map_ofNat]
      ring]
    rw [map_add, map_sub, constant, projection, hone, htwo]
    ring
  have pushSquareTimes : push ((f h - t) ^ 2 * t ^ 2) = h ^ 2 - 2 * h ^ 2 + e₂ := by
    rw [show (f h - t) ^ 2 * t ^ 2 = f (h ^ 2) * t ^ 2 - f (2 * h) * t ^ 3 + t ^ 4 by
      simp only [map_pow, map_mul, map_ofNat]
      ring]
    rw [map_add, map_sub, projection, projection, htwo, pushCubic, pushQuartic]
    ring
  change push ((f h - t) ^ 2 * _) = -4 * e₃
  rw [prod]
  rw [show (f h - t) ^ 2 * (2 * (f h * t ^ 2 + f e₃)) =
      f (2 * h) * ((f h - t) ^ 2 * t ^ 2) + f (2 * e₃) * (f h - t) ^ 2 by
    simp only [map_mul, map_ofNat]
    ring]
  rw [map_add, projection, projection, pushSquare, pushSquareTimes, hs]
  linear_combination -2 * he

/-- With the base orientation normalized on `h₁ h₂ h₃`, the computed integral is `-4`. -/
theorem integral_eq_neg_four_of_push {h₁ h₂ h₃ c : R} (integrate : R →+ ℤ)
    (hbase : integrate (h₁ * h₂ * h₃) = 1) (hc : c = -4 * (h₁ * h₂ * h₃)) :
    integrate c = -4 := by
  rw [hc, show (-4 : R) * (h₁ * h₂ * h₃) = (-4 : ℤ) • (h₁ * h₂ * h₃) by
    rw [zsmul_eq_mul]
    norm_num, map_zsmul, hbase]
  decide

end

end SymmetricMaximizer
