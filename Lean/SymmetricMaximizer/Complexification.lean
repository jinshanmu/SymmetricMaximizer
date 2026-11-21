module

public import SymmetricMaximizer.Basic
import Mathlib.Tactic

/-!
# Complexification preserves the restricted norms

The real and imaginary parts are independent for the real Lyapunov operator.
-/

@[expose] public section

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace SymmetricMaximizer

variable {ι : Type*} [Fintype ι]

/-- A real matrix with its entries embedded in the complex field. -/
noncomputable def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ := A.map Complex.ofRealHom

omit [Fintype ι] in
theorem complexify_transpose (A : Matrix ι ι ℝ) : complexify Aᵀ = (complexify A)ᵀ := rfl

omit [Fintype ι] in
theorem complexify_smul (c : ℝ) (A : Matrix ι ι ℝ) :
    complexify (c • A) = (c : ℂ) • complexify A := by
  ext i j
  simp [complexify, smul_eq_mul]

omit [Fintype ι] in
theorem complexify_transpose_eq_adjoint (A : Matrix ι ι ℝ) :
    complexify Aᵀ = (complexify A)ᴴ := by
  ext i j
  simp [complexify]

omit [Fintype ι] in
theorem complexify_skew (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) :
    (complexify A)ᵀ = -complexify A := by
  rw [← complexify_transpose, hA]
  ext i j
  simp [complexify]

theorem lyapunov_complexify (A X : Matrix ι ι ℝ) :
    lyapunov (complexify A) (complexify X) = complexify (lyapunov A X) := by
  simp [lyapunov, complexify, Matrix.map_add, Matrix.map_mul, Matrix.transpose_map]

theorem norm_complexify (X : Matrix ι ι ℝ) : ‖complexify X‖ = ‖X‖ :=
  Matrix.frobenius_norm_map_eq X _ Complex.norm_real

private theorem norm_sq_complex_parts (X : Matrix ι ι ℂ) :
    ‖X‖ ^ 2 = ‖X.map Complex.re‖ ^ 2 + ‖X.map Complex.im‖ ^ 2 := by
  simp only [frobenius_norm_sq_eq_sum, Matrix.map_apply, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply, ← sq, Finset.sum_add_distrib]

private theorem lyapunov_map_re (A : Matrix ι ι ℝ) (X : Matrix ι ι ℂ) :
    (lyapunov (complexify A) X).map Complex.re = lyapunov A (X.map Complex.re) := by
  ext i j
  simp [lyapunov, complexify, Matrix.mul_apply, Complex.re_sum, Complex.add_re, Complex.mul_re]

private theorem lyapunov_map_im (A : Matrix ι ι ℝ) (X : Matrix ι ι ℂ) :
    (lyapunov (complexify A) X).map Complex.im = lyapunov A (X.map Complex.im) := by
  ext i j
  simp [lyapunov, complexify, Matrix.mul_apply, Complex.im_sum, Complex.add_im, Complex.mul_im, mul_comm]

omit [Fintype ι] in
private theorem transpose_class_map_re (ε : ℝ) (X : Matrix ι ι ℂ) (hX : Xᵀ = (ε : ℂ) • X) :
    (X.map Complex.re)ᵀ = ε • X.map Complex.re := by
  ext i j
  have h : X j i = (ε : ℂ) * X i j := congrArg (fun M : Matrix ι ι ℂ => M i j) hX
  simpa [Complex.mul_re, smul_eq_mul] using congrArg Complex.re h

omit [Fintype ι] in
private theorem transpose_class_map_im (ε : ℝ) (X : Matrix ι ι ℂ) (hX : Xᵀ = (ε : ℂ) • X) :
    (X.map Complex.im)ᵀ = ε • X.map Complex.im := by
  ext i j
  have h : X j i = (ε : ℂ) * X i j := congrArg (fun M : Matrix ι ι ℂ => M i j) hX
  simpa [Complex.mul_im, smul_eq_mul] using congrArg Complex.im h

/-- The Frobenius restricted norm is unchanged under real-to-complex extension. -/
theorem restricted_opNorm_complexify (ε : ℝ) (A : Matrix ι ι ℝ) :
    (restricted (ε : ℂ) (complexify A)).opNorm = (restricted ε A).opNorm := by
  apply le_antisymm
  · have hc := (restricted ε A).opNorm_nonneg
    refine restricted_le _ _ hc fun X hX => ?_
    have hre := lyapunov_le ε A (X.map Complex.re) (transpose_class_map_re ε X hX)
    have him := lyapunov_le ε A (X.map Complex.im) (transpose_class_map_im ε X hX)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
    rw [norm_sq_complex_parts (lyapunov (complexify A) X), lyapunov_map_re, lyapunov_map_im,
      mul_pow, norm_sq_complex_parts X, mul_add, ← mul_pow, ← mul_pow]
    exact add_le_add ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hre)
      ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr him)
  · refine restricted_le _ _ (restricted (ε : ℂ) (complexify A)).opNorm_nonneg fun X hX => ?_
    have hC : (complexify X)ᵀ = (ε : ℂ) • complexify X := by
      rw [← complexify_transpose, hX, complexify_smul]
    have h := lyapunov_le (ε : ℂ) (complexify A) (complexify X) hC
    rw [lyapunov_complexify, norm_complexify, norm_complexify] at h
    exact h

end SymmetricMaximizer
