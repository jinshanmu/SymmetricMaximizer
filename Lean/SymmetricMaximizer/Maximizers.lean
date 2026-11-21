module

public import SymmetricMaximizer.Basic
import Mathlib.Tactic

/-!
# The complete Lyapunov norm and symmetric maximizers

The orthogonal decomposition in the manuscript's introduction.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Frobenius

namespace SymmetricMaximizer

variable {ι : Type*} [Fintype ι]

/-- The real Lyapunov operator on the whole Frobenius matrix space. -/
noncomputable def lyapunovOperator (A : Matrix ι ι ℝ) : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := lyapunov A
      map_add' := lyapunov_add A
      map_smul' := fun c X => lyapunov_smul A X c }

private noncomputable def symmetricPart (X : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 / 2 : ℝ) • (X + Xᵀ)

private noncomputable def skewPart (X : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 / 2 : ℝ) • (X - Xᵀ)

omit [Fintype ι] in
private theorem symmetricPart_transpose (X : Matrix ι ι ℝ) : (symmetricPart X)ᵀ = symmetricPart X := by
  simp [symmetricPart, add_comm]

omit [Fintype ι] in
private theorem skewPart_transpose (X : Matrix ι ι ℝ) : (skewPart X)ᵀ = (-1 : ℝ) • skewPart X := by
  simp [skewPart, sub_eq_add_neg, add_comm]

omit [Fintype ι] in
private theorem parts_sum (X : Matrix ι ι ℝ) : symmetricPart X + skewPart X = X := by
  unfold symmetricPart skewPart
  module

private theorem sum_norm_sq_of_transpose_class (S K : Matrix ι ι ℝ) (hS : Sᵀ = S)
    (hK : Kᵀ = (-1 : ℝ) • K) : ‖S + K‖ ^ 2 = ‖S‖ ^ 2 + ‖K‖ ^ 2 := by
  have h := frobeniusInner_transpose S K
  rw [hS, hK, frobeniusInner_smul_right] at h
  have ho : frobeniusInner S K = 0 := by linarith
  rw [← norm_entries (S + K)]
  change ‖entries S + entries K‖ ^ 2 = _
  rw [norm_add_sq_real, inner_entries, norm_entries, norm_entries, ho]
  ring

/-- The whole induced norm is the maximum of its two transpose restrictions. -/
theorem lyapunovOperator_opNorm (A : Matrix ι ι ℝ) :
    (lyapunovOperator A).opNorm = max (symmetricNorm A) (skewNorm A) := by
  apply le_antisymm
  · let c := max (symmetricNorm A) (skewNorm A)
    have hc : 0 ≤ c := (restricted 1 A).opNorm_nonneg.trans (le_max_left _ _)
    refine (lyapunovOperator A).opNorm_le_bound hc fun X => ?_
    let S := symmetricPart X
    let K := skewPart X
    have hs : Sᵀ = S := symmetricPart_transpose X
    have hk : Kᵀ = (-1 : ℝ) • K := skewPart_transpose X
    have hsL : (lyapunov A S)ᵀ = lyapunov A S := by rw [lyapunov_transpose, hs]
    have hkL : (lyapunov A K)ᵀ = (-1 : ℝ) • lyapunov A K := by
      rw [lyapunov_transpose, hk, lyapunov_smul]
    have hLS : ‖lyapunov A S‖ ≤ c * ‖S‖ := (lyapunov_le 1 A S (by rwa [one_smul])).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hLK : ‖lyapunov A K‖ ≤ c * ‖K‖ := (lyapunov_le (-1) A K hk).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    change ‖lyapunov A X‖ ≤ c * ‖X‖
    have hx : S + K = X := parts_sum X
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
    rw [← hx, lyapunov_add, sum_norm_sq_of_transpose_class _ _ hsL hkL, mul_pow,
      sum_norm_sq_of_transpose_class _ _ hs hk, mul_add, ← mul_pow, ← mul_pow]
    exact add_le_add ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hLS)
      ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hLK)
  · have h' (ε : ℝ) : (restricted ε A).opNorm ≤ (lyapunovOperator A).opNorm :=
      restricted_le _ _ (lyapunovOperator A).opNorm_nonneg fun X _ => (lyapunovOperator A).le_opNorm X
    exact max_le (h' 1) (h' (-1))

/-- The skew-symmetric restriction in order one has norm zero. -/
theorem skewNorm_subsingleton [Subsingleton ι] (A : Matrix ι ι ℝ) : skewNorm A = 0 := by
  apply le_antisymm ?_ (restricted (-1) A).opNorm_nonneg
  refine restricted_le _ _ (by norm_num) fun X hX => ?_
  have hzero : X = 0 := by
    ext i j
    have h : X j i = -X i j := by
      have h' := congrArg (fun M : Matrix ι ι ℝ => M i j) hX
      simpa only [neg_one_smul, Matrix.neg_apply, Matrix.transpose_apply] using h'
    rw [Subsingleton.elim j i] at h ⊢
    change X i i = 0
    linarith
  simp [hzero, lyapunov]

private theorem exists_unit_symmetric [Nonempty ι] : ∃ X : Matrix ι ι ℝ, Xᵀ = X ∧ ‖X‖ = 1 := by
  classical
  let I : Matrix ι ι ℝ := 1
  have hI : I ≠ 0 := one_ne_zero
  refine ⟨‖I‖⁻¹ • I, by simp [I], ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hI)]

/-- A symmetric unit matrix attains the full induced norm exactly when `k(A) ≤ s(A)`. -/
theorem exists_symmetric_maximizer_iff [Nonempty ι] (A : Matrix ι ι ℝ) :
    (∃ X : Matrix ι ι ℝ, Xᵀ = X ∧ ‖X‖ = 1 ∧ ‖lyapunov A X‖ = (lyapunovOperator A).opNorm) ↔
      skewNorm A ≤ symmetricNorm A := by
  rw [lyapunovOperator_opNorm]
  constructor
  · rintro ⟨X, hX, hnorm, hL⟩
    have h := lyapunov_le 1 A X (by rwa [one_smul])
    rw [hL, hnorm, mul_one] at h
    exact (le_max_right _ _).trans h
  · intro h
    rw [max_eq_left h]
    rcases (restricted 1 A).opNorm_nonneg.eq_or_lt with hzero | hpos
    · obtain ⟨X, hX, hnorm⟩ := exists_unit_symmetric (ι := ι)
      have hL := lyapunov_le 1 A X (by rwa [one_smul])
      change ‖lyapunov A X‖ ≤ symmetricNorm A * ‖X‖ at hL
      change 0 = symmetricNorm A at hzero
      rw [← hzero, zero_mul] at hL
      exact ⟨X, hX, hnorm, (le_antisymm hL (norm_nonneg _)).trans hzero⟩
    · obtain ⟨X, hunit, hnorm⟩ := exists_unit_attains_of_pos (restricted 1 A) hpos
      exact ⟨X, by simpa only [one_smul] using mem_transposeClass.mp X.property, hunit, hnorm⟩

end SymmetricMaximizer
