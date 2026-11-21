module

public import SymmetricMaximizer.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Tactic

/-!
# Unitary congruence and the Lyapunov operator

Congruence preserves transpose symmetry and the Frobenius norm and intertwines the
two Lyapunov operators in a unitary change of basis.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Frobenius

namespace SymmetricMaximizer

variable {ι : Type*} [Fintype ι]

/-- The unitary change of basis `Eᴴ A E` for the coefficient matrix. -/
def unitarySimilarity (E A : Matrix ι ι ℂ) : Matrix ι ι ℂ := Eᴴ * A * E

/-- The congruence `Eᴴ X Ē` for the input and output of the Lyapunov operator. -/
def unitaryCongruence (E X : Matrix ι ι ℂ) : Matrix ι ι ℂ := Eᴴ * X * Eᴴᵀ

theorem unitarySimilarity_adjoint (E A : Matrix ι ι ℂ) :
    unitarySimilarity E Aᴴ = (unitarySimilarity E A)ᴴ := by
  simp [unitarySimilarity, Matrix.mul_assoc]

theorem unitaryCongruence_transpose (E X : Matrix ι ι ℂ) :
    (unitaryCongruence E X)ᵀ = unitaryCongruence E Xᵀ := by
  simp [unitaryCongruence, Matrix.transpose_mul, Matrix.mul_assoc]

theorem unitaryCongruence_smul (E X : Matrix ι ι ℂ) (c : ℂ) :
    unitaryCongruence E (c • X) = c • unitaryCongruence E X := by
  simp [unitaryCongruence, Matrix.smul_mul]

variable [DecidableEq ι]

private theorem unitary_product (E : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) : E * Eᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hE

private theorem adjoint_unitary (E : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    Eᴴ ∈ Matrix.unitaryGroup ι ℂ := Unitary.star_mem hE

private theorem frobenius_norm_left_unitary (E X : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    ‖E * X‖ = ‖X‖ := by
  have hunit : Eᴴ * E = 1 := Matrix.mem_unitaryGroup_iff'.mp hE
  have h : frobeniusInner (E * X) (E * X) = frobeniusInner X X := by
    simp only [frobeniusInner_trace, conjTranspose_mul]
    calc
      trace ((Xᴴ * Eᴴ) * (E * X)) = trace (Xᴴ * (Eᴴ * E) * X) := by
        simp only [Matrix.mul_assoc]
      _ = trace (Xᴴ * X) := by simp [hunit]
  rw [frobeniusInner_self, frobeniusInner_self] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (congrArg Complex.re h)

private theorem frobenius_norm_right_unitary (E X : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    ‖X * E‖ = ‖X‖ := by
  have h : frobeniusInner (X * E) (X * E) = frobeniusInner X X := by
    simp only [frobeniusInner_trace, conjTranspose_mul]
    calc
      trace ((Eᴴ * Xᴴ) * (X * E)) = trace (Eᴴ * (Xᴴ * X) * E) := by
        simp only [Matrix.mul_assoc]
      _ = trace (E * Eᴴ * (Xᴴ * X)) := trace_mul_cycle _ _ _
      _ = trace (Xᴴ * X) := by simp [unitary_product E hE]
  rw [frobeniusInner_self, frobeniusInner_self] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (congrArg Complex.re h)

/-- The unitary group is closed and lies on the Frobenius sphere of the identity. -/
theorem isCompact_unitaryGroup : IsCompact (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have hclosed : IsClosed (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := isClosed_unitary
  refine (isCompact_closedBall (0 : Matrix ι ι ℂ) ‖(1 : Matrix ι ι ℂ)‖).of_isClosed_subset hclosed ?_
  intro E hE
  have h := frobenius_norm_left_unitary E 1 hE
  rw [mul_one] at h
  exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact h.le)

theorem norm_unitaryCongruence (E X : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    ‖unitaryCongruence E X‖ = ‖X‖ := by
  have hEH := adjoint_unitary E hE
  unfold unitaryCongruence
  rw [frobenius_norm_right_unitary _ _ (Matrix.transpose_mem_unitaryGroup_iff.mpr hEH),
    frobenius_norm_left_unitary _ _ hEH]

theorem unitaryCongruence_lyapunov (E A X : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    lyapunov (unitarySimilarity E A) (unitaryCongruence E X) = unitaryCongruence E (lyapunov A X) := by
  have hu := unitary_product E hE
  have ht : Eᴴᵀ * Eᵀ = 1 := by rw [← transpose_mul, hu, transpose_one]
  unfold lyapunov unitarySimilarity unitaryCongruence
  rw [transpose_mul, transpose_mul]
  have hleft : Eᴴ * A * E * (Eᴴ * X * Eᴴᵀ) = Eᴴ * (A * X) * Eᴴᵀ := by
    calc
      _ = Eᴴ * A * (E * Eᴴ) * (X * Eᴴᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [hu, Matrix.mul_assoc]
  have hright : Eᴴ * X * Eᴴᵀ * (Eᵀ * (Aᵀ * Eᴴᵀ)) = Eᴴ * (X * Aᵀ) * Eᴴᵀ := by
    calc
      _ = Eᴴ * X * (Eᴴᵀ * Eᵀ) * (Aᵀ * Eᴴᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [ht, Matrix.mul_assoc]
  rw [hleft, hright, Matrix.mul_add, Matrix.add_mul]

private theorem unitaryCongruence_inv (E X : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    unitaryCongruence Eᴴ (unitaryCongruence E X) = X := by
  have hu := unitary_product E hE
  have ht : Eᴴᵀ * Eᵀ = 1 := by rw [← transpose_mul, hu, transpose_one]
  unfold unitaryCongruence
  rw [conjTranspose_conjTranspose]
  calc
    _ = (E * Eᴴ) * X * (Eᴴᵀ * Eᵀ) := by simp only [Matrix.mul_assoc]
    _ = _ := by simp [hu, ht]

private theorem unitarySimilarity_inv (E A : Matrix ι ι ℂ) (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    unitarySimilarity Eᴴ (unitarySimilarity E A) = A := by
  have hu := unitary_product E hE
  unfold unitarySimilarity
  rw [conjTranspose_conjTranspose]
  calc
    _ = (E * Eᴴ) * A * (E * Eᴴ) := by simp only [Matrix.mul_assoc]
    _ = _ := by simp [hu]

private theorem restricted_opNorm_unitary_le (ε : ℂ) (E A : Matrix ι ι ℂ)
    (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    (restricted ε (unitarySimilarity E A)).opNorm ≤ (restricted ε A).opNorm := by
  refine restricted_le _ _ (restricted ε A).opNorm_nonneg fun X hX => ?_
  let Y := unitaryCongruence Eᴴ X
  have hY : Yᵀ = ε • Y := by
    change (unitaryCongruence Eᴴ X)ᵀ = ε • unitaryCongruence Eᴴ X
    rw [unitaryCongruence_transpose, hX, unitaryCongruence_smul]
  have hXY : unitaryCongruence E Y = X := by
    have h := unitaryCongruence_inv Eᴴ X (adjoint_unitary E hE)
    rw [conjTranspose_conjTranspose] at h
    exact h
  rw [← hXY, unitaryCongruence_lyapunov _ _ _ hE,
    norm_unitaryCongruence _ _ hE, norm_unitaryCongruence _ _ hE]
  exact lyapunov_le ε A Y hY

/-- A unitary change of basis preserves each Frobenius restricted operator norm. -/
theorem restricted_opNorm_unitary (ε : ℂ) (E A : Matrix ι ι ℂ)
    (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    (restricted ε (unitarySimilarity E A)).opNorm = (restricted ε A).opNorm := by
  apply le_antisymm (restricted_opNorm_unitary_le ε E A hE)
  have h := restricted_opNorm_unitary_le ε Eᴴ (unitarySimilarity E A) (adjoint_unitary E hE)
  rw [unitarySimilarity_inv _ _ hE] at h
  exact h

end SymmetricMaximizer
