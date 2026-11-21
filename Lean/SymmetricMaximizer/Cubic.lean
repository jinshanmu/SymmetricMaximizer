module

public import SymmetricMaximizer.AlternatingEigenspaces
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic

/-!
# The monic cubic in `lem:unitary`

The skew product is self-adjoint for the alternating form of its right factor.
In order six the monic square root is recovered from the three highest nonleading
coefficients of the characteristic polynomial.
-/

@[expose] public section

open Matrix Polynomial

namespace SymmetricMaximizer

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]

/-- The form associated with a transpose-skew matrix is alternating. -/
theorem isAlt_toBilin_of_skew (U : Matrix ι ι K) (hU : Uᵀ = -U) : (Matrix.toBilin' U).IsAlt := by
  intro x
  rw [Matrix.toBilin'_apply']
  have h := Matrix.dotProduct_transpose_mulVec U x x
  rw [hU, Matrix.neg_mulVec, dotProduct_neg] at h
  linear_combination -(1 / 2 : K) * h

omit [CharZero K] [DecidableEq ι] in
/-- For skew `U,V`, the endomorphism `VU` is self-adjoint for the form of `U`. -/
theorem skew_product_adjoint (U V : Matrix ι ι K) (hU : Uᵀ = -U) (hV : Vᵀ = -V) :
    (V * U)ᵀ * U = U * (V * U) := by
  simp [Matrix.transpose_mul, hU, hV, Matrix.mul_assoc]

/-- Invertibility of `U` gives a monic square root of the characteristic polynomial of `VU`. -/
theorem charpoly_skew_product_square [IsAlgClosed K] (U V : Matrix ι ι K)
    (hU : Uᵀ = -U) (hV : Vᵀ = -V) (hdet : U.det ≠ 0) :
    ∃ p : K[X], p.Monic ∧ p ^ 2 = (V * U).charpoly := by
  let C := V * U
  let F := Matrix.toBilin' U
  have hcomm : Cᵀ * U = U * C := skew_product_adjoint U V hU hV
  have hC (x y : ι → K) : F (C.toLin' x) y = F x (C.toLin' y) := by
    simp only [F, Matrix.toBilin'_apply', Matrix.toLin'_apply]
    calc
      (C *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ (Cᵀ *ᵥ (U *ᵥ y)) :=
        (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec C x (U *ᵥ y)).symm
      _ = x ⬝ᵥ (U *ᵥ (C *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec y Cᵀ U, hcomm, ← Matrix.mulVec_mulVec y U C]
  obtain ⟨p, hp, hsq⟩ := charpoly_eq_square_of_alternating F (isAlt_toBilin_of_skew U hU)
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet) C.toLin' hC
  exact ⟨p, hp, hsq.trans (Matrix.charpoly_toLin' C)⟩

omit [CharZero K] in
theorem natDegree_three_of_square_charpoly (M : Matrix ι ι K) (hι : Fintype.card ι = 6)
    (p : K[X]) (hp : p ^ 2 = M.charpoly) : p.natDegree = 3 := by
  have h := congrArg Polynomial.natDegree hp
  rw [Polynomial.natDegree_pow, Matrix.charpoly_natDegree_eq_dim, hι] at h
  omega

/-- Recover the monic cubic coefficients using the supplied scalar `half = 1/2`.
The same polynomial expressions work in the coefficient ring of a polynomial family. -/
def cubicFromSquareCoefficients {R : Type*} [CommRing R] (half : R) (p : R[X]) : Cubic R :=
  let b := half * p.coeff 5
  let c := half * (p.coeff 4 - b ^ 2)
  let d := half * (p.coeff 3 - 2 * b * c)
  ⟨1, b, c, d⟩

omit [Fintype ι] [DecidableEq ι] in
/-- For a monic cubic `p`, extracting the coefficients of `p²` recovers `p`. -/
theorem cubicFromSquareCoefficients_toPoly (p : K[X]) (hm : p.Monic) (hd : p.natDegree = 3) :
    (cubicFromSquareCoefficients (1 / 2) (p ^ 2)).toPoly = p := by
  have h₃ : p.coeff 3 = 1 := hd ▸ hm
  have h₄ : p.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (hd ▸ (by decide : 3 < 4))
  have h₅ : p.coeff 5 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (hd ▸ (by decide : 3 < 5))
  have c₅ : (p ^ 2).coeff 5 = 2 * p.coeff 2 := by
    rw [pow_two, coeff_mul, show Finset.antidiagonal 5 = {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} by decide]
    norm_num [h₃, h₄, h₅]
    ring
  have c₄ : (p ^ 2).coeff 4 = 2 * p.coeff 1 + p.coeff 2 ^ 2 := by
    rw [pow_two, coeff_mul, show Finset.antidiagonal 4 = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} by decide]
    norm_num [h₃, h₄]
    ring
  have c₃ : (p ^ 2).coeff 3 = 2 * p.coeff 0 + 2 * p.coeff 2 * p.coeff 1 := by
    rw [pow_two, coeff_mul, show Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} by decide]
    norm_num [h₃]
    ring
  have hC : cubicFromSquareCoefficients (1 / 2) (p ^ 2) = ⟨1, p.coeff 2, p.coeff 1, p.coeff 0⟩ := by
    ext <;> simp [cubicFromSquareCoefficients, c₅, c₄, c₃]
  rw [hC]
  ext i
  by_cases hi : 3 < i
  · rw [Cubic.coeff_eq_zero hi, Polynomial.coeff_eq_zero_of_natDegree_lt (hd ▸ hi)]
  · have : i ≤ 3 := Nat.le_of_not_gt hi
    interval_cases i <;> simp [h₃]

theorem cubicFromSquareCoefficients_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (half : R) (p : R[X]) :
    (cubicFromSquareCoefficients half p).map f = cubicFromSquareCoefficients (f half) (p.map f) := by
  ext <;> simp [cubicFromSquareCoefficients, Cubic.map, Polynomial.coeff_map, map_ofNat]

end SymmetricMaximizer
