module

public import SymmetricMaximizer.Example
public import SymmetricMaximizer.Padding
import Mathlib.Tactic

/-!
# Sharpness in all orders at least seven

The integer counterexample `Dₙ` from the manuscript's final section.
-/

@[expose] public section

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace SymmetricMaximizer

private def allOnes (R ι : Type*) [One R] : Matrix ι ι R := of fun _ _ => 1

private theorem spectralNorm_allOnes (n : ℕ) : spectralNorm (allOnes ℝ (Fin n)) = n := by
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  have hrank : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (allOnes ℝ (Fin n)) =
      InnerProductSpace.rankOne ℝ x x := by
    have h : Matrix.toEuclideanLin (𝕜 := ℝ) (allOnes ℝ (Fin n)) =
        (InnerProductSpace.rankOne ℝ x x).toLinearMap := by
      apply (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n)).symm.injective
      rw [LinearEquiv.symm_apply_apply, InnerProductSpace.symm_toEuclideanLin_rankOne]
      ext i j
      simp [allOnes, x, Matrix.vecMulVec_apply]
    exact ContinuousLinearMap.ext fun y => DFunLike.congr_fun h y
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (allOnes ℝ (Fin n))‖ = _
  rw [hrank, InnerProductSpace.norm_rankOne, ← sq, EuclideanSpace.real_norm_sq_eq]
  simp [x]

private noncomputable def perturbation (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / (40 * (n : ℝ))) • allOnes ℝ (Fin n)

private theorem spectralNorm_perturbation {n : ℕ} (hn : 0 < n) :
    spectralNorm (perturbation n) = 1 / 40 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : spectralNorm (c • A) = ‖c‖ * spectralNorm A := by
    unfold spectralNorm
    rw [map_smul, norm_smul]
  rw [perturbation, h, spectralNorm_allOnes, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

private theorem restricted_opNorm_add_le {ι : Type*} [Fintype ι] (ε : ℝ) (A B : Matrix ι ι ℝ) :
    (restricted ε (A + B)).opNorm ≤ (restricted ε A).opNorm + (restricted ε B).opNorm := by
  rw [restricted_add]
  exact ContinuousLinearMap.opNorm_add_le _ _

private theorem restricted_opNorm_neg {ι : Type*} [Fintype ι] (ε : ℝ) (A : Matrix ι ι ℝ) :
    (restricted ε (-A)).opNorm = (restricted ε A).opNorm := by
  rw [← neg_one_smul ℝ A, restricted_opNorm_smul, norm_neg, norm_one, one_mul]

private def paddedExample {n : ℕ} (hn : 7 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  let e : Fin 7 ⊕ Fin (n - 7) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  reindex e e (zeroPad exampleSeven (Fin (n - 7)))

private theorem paddedExample_bounds {n : ℕ} (hn : 7 ≤ n) :
    symmetricNorm ((paddedExample hn).map (Int.cast : ℤ → ℝ)) < 1499 / 8 ∧
      375 / 2 < skewNorm ((paddedExample hn).map (Int.cast : ℤ → ℝ)) := by
  let e : Fin 7 ⊕ Fin (n - 7) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have he : (paddedExample hn).map (Int.cast : ℤ → ℝ) = reindex e e (zeroPad exampleSevenReal (Fin (n - 7))) := by
    change (reindex e e (zeroPad exampleSeven (Fin (n - 7)))).map Int.cast = _
    rw [← Matrix.reindex_map]
    congr 1
    simp [zeroPad, Matrix.fromBlocks_map, exampleSevenReal]
  have hgap : symmetricNorm exampleSevenReal < skewNorm exampleSevenReal :=
    exampleSeven_bounds.1.trans (exampleSeven_bounds.2.1.trans exampleSeven_bounds.2.2)
  rw [he]
  constructor
  · unfold symmetricNorm
    rw [restricted_opNorm_reindex]
    exact (symmetricNorm_zeroPad exampleSevenReal (κ := Fin (n - 7))).trans_lt exampleSeven_bounds.1
  · unfold skewNorm
    rw [restricted_opNorm_reindex]
    exact exampleSeven_bounds.2.2.trans_eq (skewNorm_zeroPad_of_gap exampleSevenReal
      (κ := Fin (n - 7)) hgap).symm

/-- For every `n ≥ 7`, the integer construction satisfies the strict threshold and
each entry is congruent to one modulo `40*n`. -/
theorem exists_integer_counterexample {n : ℕ} (hn : 7 ≤ n) :
    ∃ D : Matrix (Fin n) (Fin n) ℤ,
      (∀ i j, D i j % (40 * (n : ℤ)) = 1) ∧
      (∀ i j, D i j ≠ 0) ∧
      symmetricNorm (D.map (Int.cast : ℤ → ℝ)) < 40 * (n : ℝ) * (2999 / 16) ∧
      40 * (n : ℝ) * (2999 / 16) < skewNorm (D.map (Int.cast : ℤ → ℝ)) := by
  let A := paddedExample hn
  let AReal := A.map (Int.cast : ℤ → ℝ)
  let P := perturbation n
  let D := (40 * (n : ℤ)) • A + allOnes ℤ (Fin n)
  have hn0 : 0 < n := by omega
  have hnRe : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnInt : (7 : ℤ) ≤ n := by exact_mod_cast hn
  have hcast : D.map (Int.cast : ℤ → ℝ) = (40 * (n : ℝ)) • (AReal + P) := by
    ext i j
    simp only [D, AReal, P, perturbation, allOnes, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_ofNat, Int.cast_one, mul_one]
    field_simp
  have hmod (i j : Fin n) : D i j % (40 * (n : ℤ)) = 1 := by
    change ((40 * (n : ℤ)) * A i j + 1) % (40 * (n : ℤ)) = 1
    rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by norm_num)]
    omega
  have hnonzero (i j : Fin n) : D i j ≠ 0 := by
    intro hz
    simpa [hz] using hmod i j
  have hP := spectralNorm_perturbation hn0
  have hsP : symmetricNorm P ≤ 1 / 20 := by
    have h := lyapunov_opNorm_le_two_spectral P 1
    change spectralNorm P = 1 / 40 at hP
    rw [hP] at h
    exact h.trans (by norm_num)
  have hkP : skewNorm P ≤ 1 / 20 := by
    have h := lyapunov_opNorm_le_two_spectral P (-1)
    rw [hP] at h
    exact h.trans (by norm_num)
  have hs := restricted_opNorm_add_le 1 AReal P
  have hk := restricted_opNorm_add_le (-1) (AReal + P) (-P)
  rw [add_neg_cancel_right, restricted_opNorm_neg] at hk
  have hbounds := paddedExample_bounds hn
  have hs' : symmetricNorm (AReal + P) < 2999 / 16 := by
    change symmetricNorm (AReal + P) ≤ symmetricNorm AReal + symmetricNorm P at hs
    change symmetricNorm AReal < 1499 / 8 ∧ 375 / 2 < skewNorm AReal at hbounds
    linarith [hbounds.1]
  have hk' : 2999 / 16 < skewNorm (AReal + P) := by
    change skewNorm AReal ≤ skewNorm (AReal + P) + skewNorm P at hk
    change symmetricNorm AReal < 1499 / 8 ∧ 375 / 2 < skewNorm AReal at hbounds
    linarith [hbounds.2]
  refine ⟨D, hmod, hnonzero, ?_, ?_⟩
  · rw [hcast, symmetricNorm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_lt_mul_of_pos_left hs' (by positivity)
  · rw [hcast, skewNorm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_lt_mul_of_pos_left hk' (by positivity)

/-- A symmetric maximizer fails in every order at least seven. -/
theorem exists_strict_gap {n : ℕ} (hn : 7 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, symmetricNorm A < skewNorm A := by
  obtain ⟨D, _, _, hs, hk⟩ := exists_integer_counterexample hn
  exact ⟨D.map Int.cast, hs.trans hk⟩

end SymmetricMaximizer
