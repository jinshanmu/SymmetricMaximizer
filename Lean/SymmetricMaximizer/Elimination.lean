module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
# Symmetric elimination by completing the square

This is the pivot recurrence used in the manuscript's section on zero padding and sharpness.
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace SymmetricMaximizer

variable {K : Type*} [Field K] {n : ℕ}

/-- The quadratic form of a matrix in the coordinates `x`. -/
def quadratic (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) : K :=
  ∑ i, ∑ j, x i * M i j * x j

/-- The trailing matrix after one pivot at index zero. -/
def schur (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Matrix (Fin n) (Fin n) K :=
  of fun i j => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0

/-- The list of elimination pivots, in order. -/
def pivots : {n : ℕ} → Matrix (Fin n) (Fin n) K → List K
  | 0, _ => []
  | _n + 1, M => M 0 0 :: pivots (schur M)

theorem schur_isSymm {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hM : M.IsSymm) :
    (schur M).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  change M j.succ i.succ - M j.succ 0 * M 0 i.succ / M 0 0 =
    M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0
  rw [hM.apply i.succ j.succ, hM.apply 0 i.succ, hM.apply 0 j.succ, mul_comm (M 0 i.succ)]

private def pivotCorrection (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (x : Fin n → K) : K := (∑ j, M 0 j.succ * x j) / M 0 0

private theorem quadratic_split {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hM : M.IsSymm)
    (hd : M 0 0 ≠ 0) (x : Fin (n + 1) → K) :
    quadratic M x = M 0 0 * (x 0 + pivotCorrection M (fun i => x i.succ)) ^ 2 +
      quadratic (schur M) (fun i => x i.succ) := by
  let b := ∑ j : Fin n, M 0 j.succ * x j.succ
  let d := M 0 0
  let q := ∑ i : Fin n, ∑ j : Fin n, x i.succ * M i.succ j.succ * x j.succ
  have hfull : quadratic M x = x 0 * d * x 0 + x 0 * b + (b * x 0 + q) := by
    unfold quadratic
    simp only [Fin.sum_univ_succ, Finset.sum_add_distrib]
    rw [show (∑ j : Fin n, x 0 * M 0 j.succ * x j.succ) = x 0 * b by
      simp only [b, Finset.mul_sum, mul_assoc]]
    rw [show (∑ i : Fin n, x i.succ * M i.succ 0 * x 0) = b * x 0 by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hM.apply 0 i.succ, mul_comm (x i.succ)]]
    change x 0 * d * x 0 + b * x 0 + (x 0 * b + q) = _
    ring
  have htail : quadratic (schur M) (fun i => x i.succ) = q - b * b / d := by
    unfold quadratic
    change (∑ i : Fin n, ∑ j : Fin n, x i.succ *
      (M i.succ j.succ - M i.succ 0 * M 0 j.succ / d) * x j.succ) = _
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [div_eq_mul_inv, show b * b * d⁻¹ = b * (b * d⁻¹) by ring]
    simp only [b, Finset.sum_mul, Finset.mul_sum, div_eq_mul_inv]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM.apply 0 i.succ]
    ring
  rw [hfull, htail]
  change x 0 * d * x 0 + x 0 * b + (b * x 0 + q) =
    d * (x 0 + b / d) ^ 2 + (q - b * b / d)
  have hd' : d ≠ 0 := hd
  field_simp
  ring

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Positive pivots certify that the quadratic form is positive definite. -/
theorem quadratic_pos_of_pivots : {n : ℕ} →
    ∀ {M : Matrix (Fin n) (Fin n) K}, M.IsSymm →
    (∀ d ∈ pivots M, 0 < d) → ∀ x : Fin n → K, x ≠ 0 → 0 < quadratic M x
  | 0, _, _, _, x, hx => (hx (Subsingleton.elim x 0)).elim
  | n + 1, M, hM, hp, x, hx => by
    have hd : 0 < M 0 0 := hp _ (by simp [pivots])
    rw [quadratic_split hM hd.ne']
    by_cases ht : (fun i : Fin n => x i.succ) = 0
    · have hx0 : x 0 ≠ 0 := by
        intro h
        apply hx
        funext i
        refine Fin.cases h (fun j => congrFun ht j) i
      rw [ht]
      simpa [quadratic, pivotCorrection] using mul_pos hd (sq_pos_of_ne_zero hx0)
    · apply add_pos_of_nonneg_of_pos (mul_nonneg hd.le (sq_nonneg _))
      exact quadratic_pos_of_pivots (schur_isSymm hM)
        (fun d hd' => hp d (by simp [pivots, hd'])) _ ht

omit [IsStrictOrderedRing K] in
/-- A negative pivot, with all preceding pivots nonzero, certifies a negative value. -/
theorem exists_quadratic_neg_of_pivots : {n : ℕ} →
    ∀ {M : Matrix (Fin n) (Fin n) K}, M.IsSymm →
    (∀ d ∈ pivots M, d ≠ 0) → (∃ d ∈ pivots M, d < 0) →
    ∃ x : Fin n → K, quadratic M x < 0
  | 0, _, _, _, ⟨_, hd, _⟩ => by simp [pivots] at hd
  | n + 1, M, hM, hn, ⟨d, hd, hneg⟩ => by
    have hd0 : M 0 0 ≠ 0 := hn _ (by simp [pivots])
    rcases List.mem_cons.mp (show d ∈ M 0 0 :: pivots (schur M) from hd) with rfl | hd'
    · refine ⟨Fin.cons 1 0, ?_⟩
      rw [quadratic_split hM hd0]
      simpa [pivotCorrection, quadratic] using hneg
    · obtain ⟨y, hy⟩ := exists_quadratic_neg_of_pivots (schur_isSymm hM)
        (fun a ha => hn a (by simp [pivots, ha])) ⟨d, hd', hneg⟩
      refine ⟨Fin.cons (-pivotCorrection M y) y, ?_⟩
      simpa [quadratic_split hM hd0] using hy

end Ordered

theorem schur_map {L : Type*} [Field L] (f : K →+* L)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    schur (M.map f) = (schur M).map f := by
  ext i j
  simp [schur, map_div₀]

theorem pivots_map {L : Type*} [Field L] (f : K →+* L) :
    {n : ℕ} → ∀ M : Matrix (Fin n) (Fin n) K, pivots (M.map f) = (pivots M).map f
  | 0, _ => rfl
  | n + 1, M => by
    simp only [pivots, List.map_cons, map_apply, schur_map, pivots_map f (schur M)]

end SymmetricMaximizer
