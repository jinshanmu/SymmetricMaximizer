module

public import SymmetricMaximizer.Padding
import Mathlib.Tactic

/-!
# The symmetric comparison of an adapted skew singular pair

This is the calculation of `Δ₁ - Δminus₁` in the manuscript's proof in order six.
The block hypotheses are the conclusions of `lem:unitary`.
-/

public section

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace SymmetricMaximizer

variable {ι : Type*} [Fintype ι]

private def signedPart (ε : ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := M + ε • Mᵀ

omit [Fintype ι] in
private theorem signedPart_transpose {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (M : Matrix ι ι ℂ) :
    (signedPart ε M)ᵀ = ε • signedPart ε M := by
  rw [signedPart, transpose_add, transpose_smul, transpose_transpose, smul_add, smul_smul]
  rcases hε with rfl | rfl <;> simp [add_comm]

omit [Fintype ι] in
private theorem fromBlocks_signed {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (D X E : Matrix ι ι ℂ) (hD : Dᵀ = ε • D) (hE : Eᵀ = ε • E) :
    (fromBlocks D X (ε • Xᵀ) E)ᵀ = ε • fromBlocks D X (ε • Xᵀ) E := by
  rw [fromBlocks_transpose, fromBlocks_smul, transpose_smul, transpose_transpose, hD, hE]
  rcases hε with rfl | rfl <;> simp

private theorem lyapunov_class (B V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (ε : ℂ) (hV : Vᵀ = ε • V) :
    (lyapunov B V)ᵀ = ε • lyapunov B V := by
  rw [lyapunov_transpose, hV, lyapunov_smul]

private theorem inner_fromBlocks (A X Y D B P Q E : Matrix ι ι ℂ) :
    frobeniusInner (fromBlocks A X Y D) (fromBlocks B P Q E) =
      frobeniusInner A B + frobeniusInner X P + frobeniusInner Y Q + frobeniusInner D E := by
  simp only [frobeniusInner, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

private theorem inner_zero_left (M : Matrix ι ι ℂ) : frobeniusInner 0 M = 0 := by
  simp [frobeniusInner]

private theorem inner_signed_pair {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (X Y : Matrix ι ι ℂ) :
    frobeniusInner (ε • Xᵀ) (ε • Yᵀ) = frobeniusInner X Y := by
  rw [frobeniusInner_smul_left, frobeniusInner_smul_right, frobeniusInner_transpose, ← mul_assoc]
  rcases hε with rfl | rfl <;> simp

private theorem inner_self_re (M : Matrix ι ι ℂ) : (frobeniusInner M M).re = ‖M‖ ^ 2 := by
  have h : frobeniusInner M M = Complex.ofReal (‖M‖ ^ 2) := frobeniusInner_self M
  rw [h, Complex.ofReal_re]

private theorem inner_signedPart {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (M : Matrix ι ι ℂ) :
    2 * (frobeniusInner M (signedPart ε M)).re = ‖signedPart ε M‖ ^ 2 := by
  let S := signedPart ε M
  have htranspose : frobeniusInner (ε • Mᵀ) S = frobeniusInner M S := by
    change frobeniusInner (ε • Mᵀ) (signedPart ε M) = frobeniusInner M (signedPart ε M)
    rw [frobeniusInner_smul_left, ← frobeniusInner_transpose Mᵀ S, transpose_transpose,
      signedPart_transpose hε, frobeniusInner_smul_right, ← mul_assoc]
    rcases hε with rfl | rfl <;> simp
  have h := inner_self_re S
  change (frobeniusInner (M + ε • Mᵀ) S).re = _ at h
  rw [frobeniusInner_add_left, htranspose, Complex.add_re] at h
  change 2 * (frobeniusInner M S).re = ‖S‖ ^ 2
  linarith

private theorem norm_signedPart_sub (M : Matrix ι ι ℂ) :
    ‖signedPart 1 M‖ ^ 2 - ‖signedPart (-1) M‖ ^ 2 = 4 * (frobeniusInner M Mᵀ).re := by
  rw [← inner_signedPart (Or.inl rfl), ← inner_signedPart (Or.inr rfl)]
  simp only [signedPart, frobeniusInner_add_right, frobeniusInner_smul_right, one_mul,
    neg_mul, Complex.add_re, Complex.neg_re]
  ring

private theorem inner_move_G (X S G : Matrix ι ι ℂ) (hG : Gᴴ = Gᵀ) :
    frobeniusInner X (S * Gᵀ) = frobeniusInner (X * G) S := by
  rw [frobeniusInner_trace, frobeniusInner_trace, conjTranspose_mul, hG, trace_mul_cycle',
    Matrix.mul_assoc]

private noncomputable def delta (B U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : ℝ :=
  ‖U‖ ^ 2 + ‖V‖ ^ 2 - 2 * (frobeniusInner U (lyapunov B V)).re

private theorem delta_signedPart {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (B₁₁ B₁₂ B₂₂ G X Y : Matrix ι ι ℂ) (hG : Gᴴ = Gᵀ) :
    let S := signedPart ε (X * G)
    let T := signedPart ε (G * Y)
    delta (fromBlocks B₁₁ B₁₂ G B₂₂) (fromBlocks 0 X (ε • Xᵀ) T) (fromBlocks S Y (ε • Yᵀ) 0) =
      2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2) - 4 * (frobeniusInner X (B₁₁ * Y + Y * B₂₂ᵀ)).re -
        ‖S‖ ^ 2 - ‖T‖ ^ 2 := by
  dsimp only
  let S := signedPart ε (X * G)
  let T := signedPart ε (G * Y)
  let B := fromBlocks B₁₁ B₁₂ G B₂₂
  let U := fromBlocks 0 X (ε • Xᵀ) T
  let V := fromBlocks S Y (ε • Yᵀ) 0
  let LV := lyapunov B V
  let C := B₁₁ * Y + Y * B₂₂ᵀ
  change delta B U V = 2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2) - 4 * (frobeniusInner X C).re - ‖S‖ ^ 2 - ‖T‖ ^ 2
  have hV : Vᵀ = ε • V := fromBlocks_signed hε S Y 0 (signedPart_transpose hε _) (by simp)
  have hLV : LVᵀ = ε • LV := lyapunov_class B V ε hV
  have h₁₂ : LV.toBlocks₁₂ = C + S * Gᵀ := by
    simp [LV, B, V, C, lyapunov, fromBlocks_multiply, fromBlocks_add, fromBlocks_transpose]
    abel
  have h₂₂ : LV.toBlocks₂₂ = T := by
    simp [LV, B, V, T, lyapunov, signedPart, fromBlocks_multiply, fromBlocks_add,
      fromBlocks_transpose, transpose_mul, smul_mul]
  have h₂₁ : LV.toBlocks₂₁ = ε • (C + S * Gᵀ)ᵀ := by
    have h : LV.toBlocks₂₁ = ε • LV.toBlocks₁₂ᵀ := by
      ext i j
      exact congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ => M (Sum.inl j) (Sum.inr i)) hLV
    rw [h, h₁₂]
  have hinner : frobeniusInner U LV =
      2 * (frobeniusInner X C + frobeniusInner (X * G) S) + Complex.ofReal (‖T‖ ^ 2) := by
    rw [← fromBlocks_toBlocks LV, h₁₂, h₂₁, h₂₂]
    change frobeniusInner (fromBlocks 0 X (ε • Xᵀ) T)
      (fromBlocks LV.toBlocks₁₁ (C + S * Gᵀ) (ε • (C + S * Gᵀ)ᵀ) T) = _
    have hself : frobeniusInner T T = Complex.ofReal (‖T‖ ^ 2) := frobeniusInner_self T
    rw [inner_fromBlocks, inner_zero_left, inner_signed_pair hε, hself,
      frobeniusInner_add_right, inner_move_G X S G hG]
    ring
  have hsign : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hUnorm : ‖U‖ ^ 2 = 2 * ‖X‖ ^ 2 + ‖T‖ ^ 2 := by
    change ‖fromBlocks 0 X (ε • Xᵀ) T‖ ^ 2 = _
    rw [frobenius_norm_fromBlocks_sq, norm_smul, frobenius_norm_transpose, hsign, one_mul, norm_zero]
    ring
  have hVnorm : ‖V‖ ^ 2 = ‖S‖ ^ 2 + 2 * ‖Y‖ ^ 2 := by
    change ‖fromBlocks S Y (ε • Yᵀ) 0‖ ^ 2 = _
    rw [frobenius_norm_fromBlocks_sq, norm_smul, frobenius_norm_transpose, hsign, one_mul, norm_zero]
    ring
  have hS := inner_signedPart hε (X * G)
  change 2 * (frobeniusInner (X * G) S).re = ‖S‖ ^ 2 at hS
  unfold delta
  change ‖U‖ ^ 2 + ‖V‖ ^ 2 - 2 * (frobeniusInner U LV).re = _
  rw [hUnorm, hVnorm, hinner]
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Complex.ofReal_re]
  linarith

private theorem transpose_inner_re_nonneg (M : Matrix ι ι ℂ) (active : ι → Prop)
    (hzero : ∀ i j, ¬(active i ∧ active j) → star (M i j) * M j i = 0)
    (hsymm : ∀ i j, active i → active j → M i j = M j i) :
    0 ≤ (frobeniusInner M Mᵀ).re := by
  classical
  simp only [frobeniusInner, Complex.re_sum, Matrix.transpose_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hij : active i ∧ active j
  · rw [← hsymm i j hij.1 hij.2, mul_comm]
    change 0 ≤ (M i j * (starRingEnd ℂ) (M i j)).re
    rw [Complex.mul_conj']
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [hzero i j hij, Complex.zero_re]

private theorem lyapunov_skew_block₂₂ (B₁₁ B₁₂ G B₂₂ Y V₁₁ : Matrix ι ι ℂ) :
    (lyapunov (fromBlocks B₁₁ B₁₂ G B₂₂) (fromBlocks V₁₁ Y (-Yᵀ) 0)).toBlocks₂₂ =
      signedPart (-1) (G * Y) := by
  simp [lyapunov, signedPart, fromBlocks_multiply, fromBlocks_add, fromBlocks_transpose, transpose_mul]

private theorem lyapunov_adj_skew_block₁₁ (B₁₁ B₁₂ G B₂₂ X U₂₂ : Matrix ι ι ℂ)
    (hG : Gᴴ = G) (hGt : Gᵀ = G) :
    (lyapunov (fromBlocks B₁₁ B₁₂ G B₂₂)ᴴ (fromBlocks 0 X (-Xᵀ) U₂₂)).toBlocks₁₁ =
      signedPart (-1) (X * G) := by
  simp [lyapunov, signedPart, fromBlocks_multiply, fromBlocks_add, fromBlocks_transpose,
    fromBlocks_conjTranspose, transpose_mul, hG, hGt, add_comm]

/-- The adapted block form of a unit skew singular pair gives `1 ≤ s(B)`.

The indices where `g` is nonzero are the leading `r × r` blocks in `lem:unitary`.
-/
theorem symmetricNorm_ge_one_of_adapted_pair [DecidableEq ι]
    (B₁₁ B₁₂ B₂₂ X Y U₂₂ V₁₁ : Matrix ι ι ℂ) (g : ι → ℝ)
    (hU₂₂ : ∀ i j, g i ≠ 0 → g j ≠ 0 → U₂₂ i j = 0)
    (hV₁₁ : ∀ i j, g i ≠ 0 → g j ≠ 0 → V₁₁ i j = 0) :
    let G := diagonal (fun i => (g i : ℂ))
    let B := fromBlocks B₁₁ B₁₂ G B₂₂
    let U := fromBlocks 0 X (-Xᵀ) U₂₂
    let V := fromBlocks V₁₁ Y (-Yᵀ) 0
    ‖U‖ = 1 → ‖V‖ = 1 → lyapunov B V = U → lyapunov Bᴴ U = V → 1 ≤ symmetricNorm B := by
  dsimp only
  let G : Matrix ι ι ℂ := diagonal (fun i => (g i : ℂ))
  let B := fromBlocks B₁₁ B₁₂ G B₂₂
  let U := fromBlocks 0 X (-Xᵀ) U₂₂
  let V := fromBlocks V₁₁ Y (-Yᵀ) 0
  change ‖U‖ = 1 → ‖V‖ = 1 → lyapunov B V = U → lyapunov Bᴴ U = V → 1 ≤ symmetricNorm B
  intro hU hV hBV hBU
  have hGt : Gᵀ = G := diagonal_transpose _
  have hGa : Gᴴ = G := by simp [G, diagonal_conjTranspose]
  have hG : Gᴴ = Gᵀ := hGa.trans hGt.symm
  have hT : U₂₂ = signedPart (-1) (G * Y) :=
    (congrArg Matrix.toBlocks₂₂ hBV).symm.trans (lyapunov_skew_block₂₂ B₁₁ B₁₂ G B₂₂ Y V₁₁)
  have hS : V₁₁ = signedPart (-1) (X * G) :=
    (congrArg Matrix.toBlocks₁₁ hBU).symm.trans (lyapunov_adj_skew_block₁₁ B₁₁ B₁₂ G B₂₂ X U₂₂ hGa hGt)
  let Splus := signedPart 1 (X * G)
  let Tplus := signedPart 1 (G * Y)
  let Uplus := fromBlocks 0 X Xᵀ Tplus
  let Vplus := fromBlocks Splus Y Yᵀ 0
  have hδplus := delta_signedPart (ε := 1) (Or.inl rfl) B₁₁ B₁₂ B₂₂ G X Y hG
  have hδminus := delta_signedPart (ε := -1) (Or.inr rfl) B₁₁ B₁₂ B₂₂ G X Y hG
  simp only [one_smul] at hδplus
  simp only [neg_one_smul] at hδminus
  rw [← hS, ← hT] at hδminus
  change delta B Uplus Vplus = 2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2) -
    4 * (frobeniusInner X (B₁₁ * Y + Y * B₂₂ᵀ)).re - ‖Splus‖ ^ 2 - ‖Tplus‖ ^ 2 at hδplus
  change delta B U V = 2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2) -
    4 * (frobeniusInner X (B₁₁ * Y + Y * B₂₂ᵀ)).re - ‖V₁₁‖ ^ 2 - ‖U₂₂‖ ^ 2 at hδminus
  have hzero : delta B U V = 0 := by
    rw [delta, hBV, inner_self_re, hU, hV]
    norm_num
  have hdiff : delta B Uplus Vplus - delta B U V =
      -4 * ((frobeniusInner (X * G) (X * G)ᵀ).re + (frobeniusInner (G * Y) (G * Y)ᵀ).re) := by
    rw [hδplus, hδminus, hS, hT]
    linarith [norm_signedPart_sub (X * G), norm_signedPart_sub (G * Y)]
  have hXG : 0 ≤ (frobeniusInner (X * G) (X * G)ᵀ).re := by
    apply transpose_inner_re_nonneg _ (fun i => g i ≠ 0)
    · intro i j h
      rcases not_and_or.mp h with hi | hj
      · simp [G, Matrix.mul_diagonal, not_not.mp hi]
      · simp [G, Matrix.mul_diagonal, not_not.mp hj]
    · intro i j hi hj
      have h := hV₁₁ i j hi hj
      rw [hS] at h
      simpa only [signedPart, neg_one_smul, Matrix.add_apply, Matrix.neg_apply,
        Matrix.transpose_apply, ← sub_eq_add_neg, sub_eq_zero] using h
  have hGY : 0 ≤ (frobeniusInner (G * Y) (G * Y)ᵀ).re := by
    apply transpose_inner_re_nonneg _ (fun i => g i ≠ 0)
    · intro i j h
      rcases not_and_or.mp h with hi | hj
      · simp [G, Matrix.diagonal_mul, not_not.mp hi]
      · simp [G, Matrix.diagonal_mul, not_not.mp hj]
    · intro i j hi hj
      have h := hU₂₂ i j hi hj
      rw [hT] at h
      simpa only [signedPart, neg_one_smul, Matrix.add_apply, Matrix.neg_apply,
        Matrix.transpose_apply, ← sub_eq_add_neg, sub_eq_zero] using h
  have hδ : delta B Uplus Vplus ≤ 0 := by linarith
  have hVplus : Vplusᵀ = (1 : ℂ) • Vplus := by
    simpa only [one_smul] using
      fromBlocks_signed (Or.inl rfl) Splus Y 0 (signedPart_transpose (Or.inl rfl) _) (by simp)
  have hL := lyapunov_le 1 B Vplus hVplus
  have hcs := (Complex.re_le_norm (frobeniusInner Uplus (lyapunov B Vplus))).trans
    (norm_frobeniusInner_le Uplus (lyapunov B Vplus))
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_left hL (norm_nonneg Uplus))
  have hs : 0 ≤ symmetricNorm B := (restricted 1 B).opNorm_nonneg
  have hbound : (1 - symmetricNorm B) * (‖Uplus‖ ^ 2 + ‖Vplus‖ ^ 2) ≤ delta B Uplus Vplus := by
    change (frobeniusInner Uplus (lyapunov B Vplus)).re ≤ ‖Uplus‖ * (symmetricNorm B * ‖Vplus‖) at hcs'
    unfold delta
    nlinarith [mul_nonneg hs (sq_nonneg (‖Uplus‖ - ‖Vplus‖))]
  have hne : X ≠ 0 ∨ Y ≠ 0 := by
    by_contra! h
    have hU0 : U = 0 := by simp [U, h.1, hT, h.2, signedPart]
    rw [hU0, norm_zero] at hU
    norm_num at hU
  have hpos : 0 < ‖Uplus‖ ^ 2 + ‖Vplus‖ ^ 2 := by
    rcases hne with hX | hY
    · have hne : Uplus ≠ 0 := fun h => hX (congrArg Matrix.toBlocks₁₂ h)
      exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne)) (sq_nonneg _)
    · have hne : Vplus ≠ 0 := fun h => hY (congrArg Matrix.toBlocks₁₂ h)
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne))
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_left (hbound.trans hδ) hpos)

end SymmetricMaximizer
