module

public import SymmetricMaximizer.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Zero padding of the symmetric and skew-symmetric restrictions

The block decomposition and rank-one estimate in `eq:padding`.
-/

@[expose] public section

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace SymmetricMaximizer

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The spectral norm of a matrix, using its action on Euclidean space. -/
noncomputable def spectralNorm (A : Matrix ι ι ℝ) : ℝ := by
  classical
  exact ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A‖

theorem spectralNorm_nonneg (A : Matrix ι ι ℝ) : 0 ≤ spectralNorm A := by
  classical
  exact norm_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)

theorem norm_mul_le_spectralNorm (A : Matrix ι ι ℝ) (Y : Matrix ι κ ℝ) :
    ‖A * Y‖ ≤ spectralNorm A * ‖Y‖ := by
  classical
  let col (M : Matrix ι κ ℝ) (j : κ) : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 (fun i => M i j)
  have columns (M : Matrix ι κ ℝ) : ‖M‖ ^ 2 = ∑ j, ‖col M j‖ ^ 2 := by
    simp only [frobenius_norm_sq_eq_sum, EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs]
    exact Finset.sum_comm
  have hcol (j : κ) : ‖col (A * Y) j‖ ≤ spectralNorm A * ‖col Y j‖ := by
    exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm (col Y j)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (spectralNorm_nonneg A) (norm_nonneg _))).mp
  rw [columns, mul_pow, columns, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (spectralNorm_nonneg A) (norm_nonneg _))).mpr (hcol j)

theorem lyapunov_opNorm_le_two_spectral (A : Matrix ι ι ℝ) (ε : ℝ) :
    (restricted ε A).opNorm ≤ 2 * spectralNorm A := by
  refine restricted_le _ _ (mul_nonneg (by norm_num) (spectralNorm_nonneg A)) fun X _ => ?_
  have hright : ‖X * Aᵀ‖ ≤ spectralNorm A * ‖X‖ := by
    rw [← Matrix.frobenius_norm_transpose (X * Aᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.frobenius_norm_transpose X]
    exact norm_mul_le_spectralNorm A Xᵀ
  rw [lyapunov, two_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le_spectralNorm A X) hright)

theorem frobenius_norm_fromBlocks_sq {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix ι ι 𝕜) (Y : Matrix ι κ 𝕜) (Z : Matrix κ ι 𝕜) (D : Matrix κ κ 𝕜) :
    ‖fromBlocks A Y Z D‖ ^ 2 = ‖A‖ ^ 2 + ‖Y‖ ^ 2 + ‖Z‖ ^ 2 + ‖D‖ ^ 2 := by
  simp only [frobenius_norm_sq_eq_sum, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

private theorem norm_vecMulVec (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    ‖vecMulVec x.ofLp y.ofLp‖ = ‖x‖ * ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [frobenius_norm_sq_eq_sum, Real.norm_eq_abs, sq_abs, Matrix.vecMulVec_apply,
    mul_pow, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem lyapunov_rankOne_sq (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι)
    [DecidableEq ι] :
    ‖lyapunov A (vecMulVec x.ofLp x.ofLp)‖ ^ 2 =
      2 * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x‖ ^ 2 * ‖x‖ ^ 2 +
        2 * (x.ofLp ⬝ᵥ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x).ofLp) ^ 2 := by
  let y : EuclideanSpace ℝ ι := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x
  have hy : y.ofLp = A *ᵥ x.ofLp := Matrix.ofLp_toEuclideanCLM A x
  rw [lyapunov, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose, ← hy]
  change ‖vecMulVec y.ofLp x.ofLp + vecMulVec x.ofLp y.ofLp‖ ^ 2 =
    2 * ‖y‖ ^ 2 * ‖x‖ ^ 2 + 2 * (x.ofLp ⬝ᵥ y.ofLp) ^ 2
  simp only [frobenius_norm_sq_eq_sum, Matrix.add_apply, Real.norm_eq_abs, sq_abs,
    Matrix.vecMulVec_apply, EuclideanSpace.real_norm_sq_eq, dotProduct]
  calc
    _ = (∑ i, ∑ j, (y.ofLp i) ^ 2 * (x.ofLp j) ^ 2) +
        (∑ i, ∑ j, (x.ofLp i) ^ 2 * (y.ofLp j) ^ 2) +
        2 * (∑ i, ∑ j, (x.ofLp i * y.ofLp i) * (x.ofLp j * y.ofLp j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Testing on `xxᵀ` at a leading right singular vector gives the factor `√2`. -/
theorem sqrt_two_spectralNorm_le_symmetricNorm (A : Matrix ι ι ℝ) :
    Real.sqrt 2 * spectralNorm A ≤ symmetricNorm A := by
  classical
  by_cases hA : 0 < spectralNorm A
  · obtain ⟨x, hx, hs⟩ := exists_unit_attains_of_pos (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) hA
    have hbound := lyapunov_le 1 A (vecMulVec x.ofLp x.ofLp) (by simp [Matrix.transpose_vecMulVec])
    rw [norm_vecMulVec, hx, one_mul, mul_one] at hbound
    have hnonneg : 0 ≤ symmetricNorm A := (restricted 1 A).opNorm_nonneg
    have hsq := (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hbound
    rw [lyapunov_rankOne_sq A x, hs, hx] at hsq
    apply (sq_le_sq₀ (by positivity) hnonneg).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_trans (by
      dsimp [spectralNorm]
      nlinarith [sq_nonneg (x.ofLp ⬝ᵥ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x).ofLp)]) hsq
  · rw [le_antisymm (le_of_not_gt hA) (spectralNorm_nonneg A), mul_zero]
    exact (restricted 1 A).opNorm_nonneg

theorem spectralNorm_le_symmetricNorm (A : Matrix ι ι ℝ) : spectralNorm A ≤ symmetricNorm A := by
  have htwo : 1 ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  exact (le_mul_of_one_le_left (spectralNorm_nonneg A) htwo).trans
    (sqrt_two_spectralNorm_le_symmetricNorm A)

/-- The block diagonal matrix `A ⊕ 0`. -/
def zeroPad {R : Type*} [Zero R] (A : Matrix ι ι R) (κ : Type*) : Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  fromBlocks A 0 0 0

omit [Fintype ι] [Fintype κ] in
private theorem block_class {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (X : Matrix ι ι ℝ) (Y : Matrix ι κ ℝ) (Z : Matrix κ κ ℝ)
    (hX : Xᵀ = ε • X) (hZ : Zᵀ = ε • Z) :
    (fromBlocks X Y (ε • Yᵀ) Z)ᵀ = ε • fromBlocks X Y (ε • Yᵀ) Z := by
  rw [fromBlocks_transpose, fromBlocks_smul, transpose_smul, transpose_transpose, hX, hZ]
  rcases hε with rfl | rfl <;> simp

private theorem lyapunov_zeroPad_blocks (ε : ℝ) (A X : Matrix ι ι ℝ)
    (Y : Matrix ι κ ℝ) (Z : Matrix κ κ ℝ) :
    lyapunov (zeroPad A κ) (fromBlocks X Y (ε • Yᵀ) Z) =
      fromBlocks (lyapunov A X) (A * Y) (ε • (A * Y)ᵀ) 0 := by
  simp [lyapunov, zeroPad, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_add,
    transpose_mul, smul_mul]

private theorem block_class_norm_sq {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (X : Matrix ι ι ℝ) (Y : Matrix ι κ ℝ) (Z : Matrix κ κ ℝ) :
    ‖fromBlocks X Y (ε • Yᵀ) Z‖ ^ 2 = ‖X‖ ^ 2 + 2 * ‖Y‖ ^ 2 + ‖Z‖ ^ 2 := by
  have h : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  rw [frobenius_norm_fromBlocks_sq, norm_smul, Matrix.frobenius_norm_transpose, h, one_mul]
  ring

private theorem pad_norm_upper (A : Matrix ι ι ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (restricted ε (zeroPad A κ)).opNorm ≤ max (restricted ε A).opNorm (spectralNorm A) := by
  let c := max (restricted ε A).opNorm (spectralNorm A)
  have hc : 0 ≤ c := (spectralNorm_nonneg A).trans (le_max_right _ _)
  refine restricted_le _ _ hc fun M hM => ?_
  let X := M.toBlocks₁₁
  let Y := M.toBlocks₁₂
  let Z := M.toBlocks₂₂
  have hX : Xᵀ = ε • X := congrArg Matrix.toBlocks₁₁ hM
  have hY : M.toBlocks₂₁ = ε • Yᵀ := by
    ext i j
    exact congrArg (fun N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ => N (Sum.inl j) (Sum.inr i)) hM
  have hdecomp : M = fromBlocks X Y (ε • Yᵀ) Z := by
    conv_lhs => rw [← fromBlocks_toBlocks M, hY]
  have hx : ‖lyapunov A X‖ ≤ c * ‖X‖ := (lyapunov_le ε A X hX).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hy : ‖A * Y‖ ≤ c * ‖Y‖ := (norm_mul_le_spectralNorm A Y).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [hdecomp, lyapunov_zeroPad_blocks, mul_pow, block_class_norm_sq hε, block_class_norm_sq hε]
  have hx2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hx
  have hy2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hy
  rw [mul_pow] at hx2 hy2
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg ‖Z‖)]

theorem norm_le_zeroPad (A : Matrix ι ι ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (restricted ε A).opNorm ≤ (restricted ε (zeroPad A κ)).opNorm := by
  refine restricted_le _ _ (restricted ε (zeroPad A κ)).opNorm_nonneg fun X hX => ?_
  have h := lyapunov_le ε (zeroPad A κ) (fromBlocks X 0 (ε • (0 : Matrix ι κ ℝ)ᵀ) 0)
    (block_class hε X 0 0 hX (by simp))
  rw [lyapunov_zeroPad_blocks, show A * (0 : Matrix ι κ ℝ) = 0 by simp] at h
  have hnorm (T : Matrix ι ι ℝ) :
      ‖fromBlocks T (0 : Matrix ι κ ℝ) (ε • (0 : Matrix ι κ ℝ)ᵀ) 0‖ = ‖T‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [block_class_norm_sq hε]
    simp
  simpa only [hnorm] using h

private theorem spectralNorm_le_zeroPad [Nonempty κ] (A : Matrix ι ι ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) : spectralNorm A ≤ (restricted ε (zeroPad A κ)).opNorm := by
  classical
  let j : κ := Classical.choice ‹Nonempty κ›
  let e : EuclideanSpace ℝ κ := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  refine (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).opNorm_le_bound
    (restricted ε (zeroPad A κ)).opNorm_nonneg fun x => ?_
  let Y := vecMulVec x.ofLp e.ofLp
  have hY : ‖Y‖ = ‖x‖ := by rw [norm_vecMulVec, he, mul_one]
  have hAY : ‖A * Y‖ = ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x‖ := by
    rw [show A * Y = vecMulVec (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x).ofLp e.ofLp by
      rw [Matrix.ofLp_toEuclideanCLM, Matrix.mul_vecMulVec], norm_vecMulVec, he, mul_one]
  have h := lyapunov_le ε (zeroPad A κ) (fromBlocks 0 Y (ε • Yᵀ) 0)
    (block_class hε 0 Y 0 (by simp) (by simp))
  have hnorm (W : Matrix ι κ ℝ) : ‖fromBlocks 0 W (ε • Wᵀ) 0‖ = Real.sqrt 2 * ‖W‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [block_class_norm_sq hε, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  rw [lyapunov_zeroPad_blocks, show lyapunov A 0 = 0 by simp [lyapunov], hnorm, hnorm, hAY, hY] at h
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  exact (mul_le_mul_iff_right₀ hsqrt).mp (h.trans_eq (mul_left_comm _ _ _))

/-- In each transpose class, padding adds an orthogonal component of spectral norm `‖A‖₂`. -/
theorem restricted_zeroPad [Nonempty κ] (A : Matrix ι ι ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (restricted ε (zeroPad A κ)).opNorm = max (restricted ε A).opNorm (spectralNorm A) := by
  exact le_antisymm (pad_norm_upper A hε)
    (max_le (norm_le_zeroPad A hε) (spectralNorm_le_zeroPad A hε))

theorem symmetricNorm_zeroPad (A : Matrix ι ι ℝ) : symmetricNorm (zeroPad A κ) = symmetricNorm A := by
  exact le_antisymm ((pad_norm_upper A (Or.inl rfl)).trans
    (max_le le_rfl (spectralNorm_le_symmetricNorm A))) (norm_le_zeroPad A (Or.inl rfl))

theorem skewNorm_zeroPad [Nonempty κ] (A : Matrix ι ι ℝ) :
    skewNorm (zeroPad A κ) = max (skewNorm A) (spectralNorm A) :=
  restricted_zeroPad A (Or.inr rfl)

theorem skewNorm_zeroPad_of_gap (A : Matrix ι ι ℝ) (h : symmetricNorm A < skewNorm A) :
    skewNorm (zeroPad A κ) = skewNorm A := by
  exact le_antisymm ((pad_norm_upper A (Or.inr rfl)).trans
    (max_le le_rfl ((spectralNorm_le_symmetricNorm A).trans h.le)))
    (norm_le_zeroPad A (Or.inr rfl))

private theorem lyapunov_reindex (e : ι ≃ κ) (A X : Matrix ι ι ℝ) :
    lyapunov (reindex e e A) (reindex e e X) = reindex e e (lyapunov A X) := by
  simp [lyapunov, Matrix.reindex_apply, Matrix.submatrix_add]

private theorem norm_reindex (e : ι ≃ κ) (X : Matrix ι ι ℝ) : ‖reindex e e X‖ = ‖X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq_eq_sum, frobenius_norm_sq_eq_sum]
  refine Fintype.sum_equiv e.symm _ _ fun i => ?_
  exact Fintype.sum_equiv e.symm _ _ fun j => rfl

private theorem restricted_opNorm_reindex_le (e : ι ≃ κ) (ε : ℝ) (A : Matrix ι ι ℝ) :
    (restricted ε (reindex e e A)).opNorm ≤ (restricted ε A).opNorm := by
  refine restricted_le _ _ (restricted ε A).opNorm_nonneg fun X hX => ?_
  let Y := reindex e.symm e.symm X
  have heX : reindex e e Y = X := (reindex e e).apply_symm_apply X
  have hY : Yᵀ = ε • Y := by
    change (reindex e.symm e.symm X)ᵀ = _
    rw [Matrix.transpose_reindex, hX]
    rfl
  rw [← heX, lyapunov_reindex, norm_reindex, norm_reindex]
  exact lyapunov_le ε A Y hY

/-- Relabeling rows and columns together preserves the restricted Frobenius norm. -/
theorem restricted_opNorm_reindex (e : ι ≃ κ) (ε : ℝ) (A : Matrix ι ι ℝ) :
    (restricted ε (reindex e e A)).opNorm = (restricted ε A).opNorm := by
  apply le_antisymm (restricted_opNorm_reindex_le e ε A)
  have h := restricted_opNorm_reindex_le e.symm ε (reindex e e A)
  rw [show reindex e.symm e.symm (reindex e e A) = A from (reindex e e).symm_apply_apply A] at h
  exact h

end SymmetricMaximizer
