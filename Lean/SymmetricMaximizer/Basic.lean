module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Frobenius restricted norms of the Lyapunov operator

Notation and basic operator facts from the introduction of `lyapunov-all-orders.tex`.
-/

@[expose] public section

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace SymmetricMaximizer

section Algebra

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- The Lyapunov operator with coefficient matrix `A`. -/
def lyapunov (A X : Matrix ι ι R) : Matrix ι ι R := A * X + X * Aᵀ

theorem lyapunov_add (A X Y : Matrix ι ι R) :
    lyapunov A (X + Y) = lyapunov A X + lyapunov A Y := by
  simp only [lyapunov, mul_add, add_mul]
  abel

theorem lyapunov_smul (A X : Matrix ι ι R) (c : R) :
    lyapunov A (c • X) = c • lyapunov A X := by
  simp [lyapunov, smul_mul, smul_add]

theorem lyapunov_add_left (A B X : Matrix ι ι R) :
    lyapunov (A + B) X = lyapunov A X + lyapunov B X := by
  simp only [lyapunov, transpose_add, mul_add, add_mul]
  abel

theorem lyapunov_smul_left (A X : Matrix ι ι R) (c : R) :
    lyapunov (c • A) X = c • lyapunov A X := by
  simp [lyapunov, smul_mul, smul_add]

theorem lyapunov_transpose (A X : Matrix ι ι R) :
    (lyapunov A X)ᵀ = lyapunov A Xᵀ := by
  simp [lyapunov, transpose_mul, add_comm]

/-- The transpose eigenspace. Eigenvalues `1` and `-1` specify the symmetric and
skew-symmetric subspaces. -/
def transposeClass (ι R : Type*) [CommRing R] (ε : R) : Submodule R (Matrix ι ι R) where
  carrier := {X | Xᵀ = ε • X}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change Xᵀ = ε • X at hX
    change Yᵀ = ε • Y at hY
    simp [hX, hY, smul_add]
  smul_mem' c {X} hX := by
    change Xᵀ = ε • X at hX
    simp [hX, smul_comm c ε X]

omit [Fintype ι] in
@[simp] theorem mem_transposeClass {ε : R} {X : Matrix ι ι R} :
    X ∈ transposeClass ι R ε ↔ Xᵀ = ε • X := Iff.rfl

/-- The Lyapunov operator as a linear map on a transpose class. -/
def restrictedLinear (ε : R) (A : Matrix ι ι R) :
    transposeClass ι R ε →ₗ[R] transposeClass ι R ε where
  toFun X := ⟨lyapunov A X, by
    rw [mem_transposeClass, lyapunov_transpose, mem_transposeClass.mp X.property,
      lyapunov_smul]⟩
  map_add' X Y := Subtype.ext (lyapunov_add A X Y)
  map_smul' c X := Subtype.ext (lyapunov_smul A X c)

end Algebra

section Norm

variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ]

/-- The restricted Lyapunov operator with the Frobenius norm on its domain and range. -/
noncomputable def restricted (ε : 𝕜) (A : Matrix ι ι 𝕜) :
    transposeClass ι 𝕜 ε →L[𝕜] transposeClass ι 𝕜 ε :=
  (restrictedLinear ε A).toContinuousLinearMap

@[simp] theorem restricted_apply (ε : 𝕜) (A : Matrix ι ι 𝕜) (X : transposeClass ι 𝕜 ε) :
    ((restricted ε A X : transposeClass ι 𝕜 ε) : Matrix ι ι 𝕜) = lyapunov A X := rfl

/-- The symmetric restricted operator norm `s(A)`. -/
noncomputable def symmetricNorm (A : Matrix ι ι 𝕜) : ℝ := (restricted 1 A).opNorm

/-- The skew-symmetric restricted operator norm `k(A)`. -/
noncomputable def skewNorm (A : Matrix ι ι 𝕜) : ℝ := (restricted (-1) A).opNorm

theorem restricted_add (ε : 𝕜) (A B : Matrix ι ι 𝕜) :
    restricted ε (A + B) = restricted ε A + restricted ε B := by
  ext X : 1
  exact Subtype.ext (lyapunov_add_left A B X)

theorem restricted_smul (ε c : 𝕜) (A : Matrix ι ι 𝕜) :
    restricted ε (c • A) = c • restricted ε A := by
  ext X : 1
  exact Subtype.ext (lyapunov_smul_left A X c)

theorem lyapunov_le (ε : 𝕜) (A X : Matrix ι ι 𝕜) (hX : Xᵀ = ε • X) :
    ‖lyapunov A X‖ ≤ (restricted ε A).opNorm * ‖X‖ :=
  (restricted ε A).le_opNorm ⟨X, hX⟩

theorem restricted_le (ε : 𝕜) (A : Matrix ι ι 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ X : Matrix ι ι 𝕜, Xᵀ = ε • X → ‖lyapunov A X‖ ≤ c * ‖X‖) :
    (restricted ε A).opNorm ≤ c :=
  (restricted ε A).opNorm_le_bound hc fun X => h X X.property

theorem restricted_opNorm_smul (ε c : 𝕜) (A : Matrix ι ι 𝕜) :
    (restricted ε (c • A)).opNorm = ‖c‖ * (restricted ε A).opNorm := by
  apply le_antisymm
  · apply restricted_le _ _ (mul_nonneg (norm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _))
    intro X hX
    rw [lyapunov_smul_left, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (lyapunov_le ε A X hX) (norm_nonneg _)
  · by_cases hc : c = 0
    · subst c
      rw [norm_zero, zero_mul]
      exact (restricted ε ((0 : 𝕜) • A)).opNorm_nonneg
    · rw [mul_comm ‖c‖, ← le_div_iff₀ (norm_pos_iff.mpr hc)]
      apply restricted_le _ _ (div_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
      intro X hX
      have h := lyapunov_le ε (c • A) X hX
      rw [lyapunov_smul_left, norm_smul] at h
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ (norm_pos_iff.mpr hc)).mpr (by rwa [mul_comm ‖lyapunov A X‖])

theorem symmetricNorm_smul (c : 𝕜) (A : Matrix ι ι 𝕜) :
    symmetricNorm (c • A) = ‖c‖ * symmetricNorm A := restricted_opNorm_smul 1 c A

theorem skewNorm_smul (c : 𝕜) (A : Matrix ι ι 𝕜) :
    skewNorm (c • A) = ‖c‖ * skewNorm A := restricted_opNorm_smul (-1) c A

/-- The Frobenius inner product, conjugate linear in its first argument. -/
def frobeniusInner (X Y : Matrix ι κ 𝕜) : 𝕜 := ∑ i, ∑ j, star (X i j) * Y i j

/-- A rectangular matrix as a vector in the Euclidean space of its entries. -/
def entries (X : Matrix ι κ 𝕜) : EuclideanSpace 𝕜 (ι × κ) :=
  WithLp.toLp 2 fun ij => X ij.1 ij.2

theorem inner_entries (X Y : Matrix ι κ 𝕜) :
    inner 𝕜 (entries X) (entries Y) = frobeniusInner X Y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, entries, frobeniusInner,
    Fintype.sum_prod_type, mul_comm]

theorem norm_entries (X : Matrix ι κ 𝕜) : ‖entries X‖ = ‖X‖ := by
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp [entries, Fintype.sum_prod_type]

theorem frobenius_norm_sq_eq_sum (X : Matrix ι κ 𝕜) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [← norm_entries, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem frobeniusInner_self (X : Matrix ι κ 𝕜) :
    frobeniusInner X X = (‖X‖ ^ 2 : ℝ) := by
  rw [← inner_entries, inner_self_eq_norm_sq_to_K, norm_entries, RCLike.ofReal_pow]

theorem norm_frobeniusInner_le (X Y : Matrix ι κ 𝕜) :
    ‖frobeniusInner X Y‖ ≤ ‖X‖ * ‖Y‖ := by
  rw [← inner_entries, ← norm_entries X, ← norm_entries Y]
  exact norm_inner_le_norm _ _

theorem frobeniusInner_trace (X Y : Matrix ι κ 𝕜) :
    frobeniusInner X Y = trace (Xᴴ * Y) := by
  simp only [frobeniusInner, trace, diag, Matrix.mul_apply, conjTranspose_apply]
  exact Finset.sum_comm

theorem frobeniusInner_transpose (X Y : Matrix ι κ 𝕜) :
    frobeniusInner Xᵀ Yᵀ = frobeniusInner X Y := by
  exact Finset.sum_comm

theorem frobeniusInner_add_left (X Y Z : Matrix ι κ 𝕜) :
    frobeniusInner (X + Y) Z = frobeniusInner X Z + frobeniusInner Y Z := by
  simp only [frobeniusInner, Matrix.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem frobeniusInner_add_right (X Y Z : Matrix ι κ 𝕜) :
    frobeniusInner X (Y + Z) = frobeniusInner X Y + frobeniusInner X Z := by
  simp only [frobeniusInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem frobeniusInner_smul_left (c : 𝕜) (X Y : Matrix ι κ 𝕜) :
    frobeniusInner (c • X) Y = star c * frobeniusInner X Y := by
  simp only [frobeniusInner, Matrix.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem frobeniusInner_smul_right (c : 𝕜) (X Y : Matrix ι κ 𝕜) :
    frobeniusInner X (c • Y) = c * frobeniusInner X Y := by
  simp only [frobeniusInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem star_frobeniusInner (X Y : Matrix ι κ 𝕜) :
    star (frobeniusInner X Y) = frobeniusInner Y X := by
  simp only [frobeniusInner, star_sum, star_mul, star_star]

theorem lyapunov_adjoint (A X Y : Matrix ι ι 𝕜) :
    frobeniusInner X (lyapunov A Y) = frobeniusInner (lyapunov Aᴴ X) Y := by
  simp only [frobeniusInner_trace, lyapunov, Matrix.mul_add, Matrix.add_mul, trace_add,
    conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.mul_assoc]
  rw [trace_mul_cycle' Xᴴ Y Aᵀ]

end Norm

section Attainment

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A positive operator norm in finite dimension is attained on the unit sphere. -/
theorem exists_unit_attains_of_pos (f : E →L[ℝ] F) (hf : 0 < ‖f‖) :
    ∃ x, ‖x‖ = 1 ∧ ‖f x‖ = ‖f‖ := by
  have hne : f ≠ 0 := norm_pos_iff.mp hf
  obtain ⟨u, hu⟩ := Function.ne_iff.mp (show (f : E → F) ≠ 0 from fun h =>
    hne (DFunLike.coe_injective h))
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (map_zero f)
  have unit (x : E) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr hx
  have hn : (Metric.sphere (0 : E) 1).Nonempty :=
    ⟨‖u‖⁻¹ • u, mem_sphere_zero_iff_norm.mpr (unit u hu0)⟩
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hn
    (f.continuous.norm.continuousOn)
  have hx1 := mem_sphere_zero_iff_norm.mp hx
  refine ⟨x, hx1, le_antisymm (by simpa [hx1] using f.le_opNorm x) ?_⟩
  exact ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy =>
    hmax (mem_sphere_zero_iff_norm.mpr hy)

end Attainment

end SymmetricMaximizer
