module

public import SymmetricMaximizer.BlockComparison
public import SymmetricMaximizer.Complexification
public import SymmetricMaximizer.Unitary
import Mathlib.Tactic

/-!
# Reduction of the order-six comparison to the adapted unitary basis

The normalization, singular equations, and comparison apply once the adapted basis in
`lem:unitary` exists. The last theorem gives the manuscript's reduction of lower orders to six.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Frobenius

namespace SymmetricMaximizer

section SingularPair

variable {ι : Type*} [Fintype ι]

/-- A skew restriction of norm one has a unit singular pair with both singular equations. -/
theorem exists_unit_skew_singular_pair (A : Matrix ι ι ℝ) (hA : skewNorm A = 1) :
    ∃ U V : Matrix ι ι ℝ, Uᵀ = -U ∧ Vᵀ = -V ∧ ‖U‖ = 1 ∧ ‖V‖ = 1 ∧
      lyapunov A V = U ∧ lyapunov Aᵀ U = V := by
  have hp : 0 < skewNorm A := hA.symm ▸ zero_lt_one
  obtain ⟨v, hv, hAv⟩ := exists_unit_attains_of_pos (restricted (-1) A) hp
  let V : Matrix ι ι ℝ := v
  let U := lyapunov A V
  have hV : ‖V‖ = 1 := hv
  have hU : ‖U‖ = 1 := hAv.trans hA
  have hVs : Vᵀ = (-1 : ℝ) • V := v.property
  have hUs : Uᵀ = (-1 : ℝ) • U := by
    change (lyapunov A V)ᵀ = (-1 : ℝ) • lyapunov A V
    rw [lyapunov_transpose, hVs, lyapunov_smul]
  let W := lyapunov Aᵀ U
  have hWs : Wᵀ = (-1 : ℝ) • W := by
    change (lyapunov Aᵀ U)ᵀ = (-1 : ℝ) • lyapunov Aᵀ U
    rw [lyapunov_transpose, hUs, lyapunov_smul]
  have adjoint_eq (X : Matrix ι ι ℝ) : frobeniusInner U (lyapunov A X) = frobeniusInner W X := by
    simpa only [W, Matrix.conjTranspose_eq_transpose_of_trivial] using lyapunov_adjoint A U X
  have hnorm : ‖lyapunov A W‖ ≤ ‖W‖ := by
    have h := lyapunov_le (-1) A W hWs
    change ‖lyapunov A W‖ ≤ skewNorm A * ‖W‖ at h
    rwa [hA, one_mul] at h
  have hWsq : ‖W‖ ^ 2 ≤ ‖W‖ := calc
    ‖W‖ ^ 2 = frobeniusInner U (lyapunov A W) := (adjoint_eq W).trans (frobeniusInner_self W) |>.symm
    _ ≤ ‖frobeniusInner U (lyapunov A W)‖ := le_abs_self _
    _ ≤ ‖U‖ * ‖lyapunov A W‖ := norm_frobeniusInner_le _ _
    _ ≤ ‖W‖ := by rw [hU, one_mul]; exact hnorm
  have hW : ‖W‖ ≤ 1 := by
    by_contra! h
    have h' := mul_lt_mul_of_pos_left h (zero_lt_one.trans h)
    nlinarith
  have hWV : frobeniusInner W V = 1 := by
    rw [← adjoint_eq V]
    change frobeniusInner U U = 1
    rw [frobeniusInner_self, hU]
    norm_num
  have hdiff : ‖W - V‖ ^ 2 = ‖W‖ ^ 2 - 2 + 1 := by
    rw [← norm_entries (W - V)]
    change ‖entries W - entries V‖ ^ 2 = _
    rw [norm_sub_sq_real, norm_entries, norm_entries, inner_entries, hWV, hV]
    ring
  have hsq := (sq_le_sq₀ (norm_nonneg W) zero_le_one).mpr hW
  have hzero : ‖W - V‖ = 0 := by nlinarith [sq_nonneg ‖W - V‖, norm_nonneg (W - V)]
  have hWVeq : W = V := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact ⟨U, V, by simpa only [neg_one_smul] using hUs, by simpa only [neg_one_smul] using hVs,
    hU, hV, rfl, hWVeq⟩

end SingularPair

/-- The two three-dimensional halves of the order-six block decomposition. -/
abbrev OrderSixIndices := Fin 3 ⊕ Fin 3

/-- The block equations and vanishing conditions in `eq:unitary-blocks`. -/
structure AdaptedBlockForm (B U V : Matrix OrderSixIndices OrderSixIndices ℂ) where
  /-- The top-left block of the transformed coefficient matrix. -/
  B₁₁ : Matrix (Fin 3) (Fin 3) ℂ
  /-- The top-right block of the transformed coefficient matrix. -/
  B₁₂ : Matrix (Fin 3) (Fin 3) ℂ
  /-- The bottom-right block of the transformed coefficient matrix. -/
  B₂₂ : Matrix (Fin 3) (Fin 3) ℂ
  /-- The top-right block of the transformed left skew matrix. -/
  X : Matrix (Fin 3) (Fin 3) ℂ
  /-- The top-right block of the transformed right skew matrix. -/
  Y : Matrix (Fin 3) (Fin 3) ℂ
  /-- The bottom-right block of the transformed left skew matrix. -/
  U₂₂ : Matrix (Fin 3) (Fin 3) ℂ
  /-- The top-left block of the transformed right skew matrix. -/
  V₁₁ : Matrix (Fin 3) (Fin 3) ℂ
  /-- The diagonal entries of the bottom-left coefficient block in decreasing order. -/
  g : Fin 3 → ℝ
  g_nonneg : ∀ i, 0 ≤ g i
  g_antitone : Antitone g
  g_last_zero : g 2 = 0
  coefficient_eq : B = fromBlocks B₁₁ B₁₂ (diagonal fun i => (g i : ℂ)) B₂₂
  left_eq : U = fromBlocks 0 X (-Xᵀ) U₂₂
  right_eq : V = fromBlocks V₁₁ Y (-Yᵀ) 0
  leading_left_zero : ∀ i j, g i ≠ 0 → g j ≠ 0 → U₂₂ i j = 0
  leading_right_zero : ∀ i j, g i ≠ 0 → g j ≠ 0 → V₁₁ i j = 0

/-- Existence of the adapted unitary basis for the real matrices in `lem:unitary`. -/
def HasAdaptedBasis (B U V : Matrix OrderSixIndices OrderSixIndices ℝ) : Prop :=
  ∃ E ∈ Matrix.unitaryGroup OrderSixIndices ℂ,
    Nonempty (AdaptedBlockForm (unitarySimilarity E (complexify B))
      (unitaryCongruence E (complexify U)) (unitaryCongruence E (complexify V)))

/-- The order-six norm comparison follows from the adapted-basis lemma. -/
theorem skewNorm_le_symmetricNorm_of_adaptedBasis
    (hAdapted : ∀ B U V : Matrix OrderSixIndices OrderSixIndices ℝ,
      Uᵀ = -U → Vᵀ = -V → HasAdaptedBasis B U V)
    (A : Matrix OrderSixIndices OrderSixIndices ℝ) : skewNorm A ≤ symmetricNorm A := by
  by_cases hk : skewNorm A = 0
  · rw [hk]
    exact (restricted 1 A).opNorm_nonneg
  let c := skewNorm A
  let B := c⁻¹ • A
  have hc : 0 < c := lt_of_le_of_ne (restricted (-1) A).opNorm_nonneg (Ne.symm hk)
  have hB : skewNorm B = 1 := by
    change skewNorm (c⁻¹ • A) = 1
    rw [skewNorm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    exact inv_mul_cancel₀ hc.ne'
  obtain ⟨U, V, hU, hV, hnU, hnV, hBU, hBV⟩ := exists_unit_skew_singular_pair B hB
  obtain ⟨E, hE, ⟨blocks⟩⟩ := hAdapted B U V hU hV
  let Bhat := unitarySimilarity E (complexify B)
  let Uhat := unitaryCongruence E (complexify U)
  let Vhat := unitaryCongruence E (complexify V)
  have hLV : lyapunov Bhat Vhat = Uhat := by
    change lyapunov (unitarySimilarity E (complexify B)) (unitaryCongruence E (complexify V)) = _
    rw [unitaryCongruence_lyapunov _ _ _ hE, lyapunov_complexify, hBU]
  have hLU : lyapunov Bhatᴴ Uhat = Vhat := by
    change lyapunov (unitarySimilarity E (complexify B))ᴴ (unitaryCongruence E (complexify U)) = _
    rw [← unitarySimilarity_adjoint, ← complexify_transpose_eq_adjoint,
      unitaryCongruence_lyapunov _ _ _ hE, lyapunov_complexify, hBV]
  have hUnitU : ‖Uhat‖ = 1 := (norm_unitaryCongruence _ _ hE).trans ((norm_complexify U).trans hnU)
  have hUnitV : ‖Vhat‖ = 1 := (norm_unitaryCongruence _ _ hE).trans ((norm_complexify V).trans hnV)
  have hShat : 1 ≤ symmetricNorm Bhat := by
    change 1 ≤ symmetricNorm (unitarySimilarity E (complexify B))
    rw [blocks.coefficient_eq]
    apply symmetricNorm_ge_one_of_adapted_pair _ _ _ blocks.X blocks.Y blocks.U₂₂ blocks.V₁₁
      blocks.g blocks.leading_left_zero blocks.leading_right_zero
    · rw [← blocks.left_eq]; exact hUnitU
    · rw [← blocks.right_eq]; exact hUnitV
    · rw [← blocks.left_eq, ← blocks.right_eq, ← blocks.coefficient_eq]; exact hLV
    · rw [← blocks.left_eq, ← blocks.right_eq, ← blocks.coefficient_eq]; exact hLU
  have hS : 1 ≤ symmetricNorm B := by
    change 1 ≤ (restricted 1 (unitarySimilarity E (complexify B))).opNorm at hShat
    rw [restricted_opNorm_unitary _ _ _ hE, ← Complex.ofReal_one, restricted_opNorm_complexify] at hShat
    exact hShat
  change 1 ≤ symmetricNorm (c⁻¹ • A) at hS
  rw [symmetricNorm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), ← div_eq_inv_mul] at hS
  simpa only [one_mul] using (le_div_iff₀ hc).mp hS

/-- A proof at order six gives the comparison in every smaller order by zero padding. -/
theorem skewNorm_le_symmetricNorm_of_order_six
    (hSix : ∀ A : Matrix (Fin 6) (Fin 6) ℝ, skewNorm A ≤ symmetricNorm A)
    {n : ℕ} (hn : n ≤ 6) (A : Matrix (Fin n) (Fin n) ℝ) : skewNorm A ≤ symmetricNorm A := by
  let e : Fin n ⊕ Fin (6 - n) ≃ Fin 6 := finSumFinEquiv.trans (finCongr (by omega))
  let B := zeroPad A (Fin (6 - n))
  have h := hSix (reindex e e B)
  unfold skewNorm symmetricNorm at h
  rw [restricted_opNorm_reindex, restricted_opNorm_reindex] at h
  exact (norm_le_zeroPad (κ := Fin (6 - n)) A (Or.inr rfl)).trans
    (h.trans_eq (symmetricNorm_zeroPad A))

end SymmetricMaximizer
