module

public import SymmetricMaximizer.AdaptedBasisClosure
public import SymmetricMaximizer.Cubic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-!
# The dense set of skew pairs in `lem:unitary`

The determinant–discriminant polynomial is nonzero on the displayed example.
On any line between a skew pair and that example the exceptional parameters are finite.
-/

@[expose] public section

open Matrix Polynomial Set
open scoped Matrix.Norms.Frobenius

namespace SymmetricMaximizer

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

/-- The polynomial `det U det V discr(q)` in the entries of the two matrices. -/
noncomputable def skewPairDiscriminant (half : R) (U V : Matrix ι ι R) : R :=
  U.det * V.det * (cubicFromSquareCoefficients half (V * U).charpoly).discr

theorem skewPairDiscriminant_map (f : R →+* S) (half : R) (U V : Matrix ι ι R) :
    f (skewPairDiscriminant half U V) = skewPairDiscriminant (f half) (U.map f) (V.map f) := by
  have hd (p : Cubic R) : f p.discr = (p.map f).discr := by simp [Cubic.discr, Cubic.map, map_ofNat]
  rw [skewPairDiscriminant, map_mul, map_mul, RingHom.map_det, RingHom.map_det, hd,
    cubicFromSquareCoefficients_map, ← Matrix.charpoly_map, Matrix.map_mul, skewPairDiscriminant]
  rfl

/-- A real skew pair in order six with nonzero determinant–discriminant product. -/
def IsGenericSkewPair (U V : Matrix OrderSixIndices OrderSixIndices ℝ) : Prop :=
  Uᵀ = -U ∧ Vᵀ = -V ∧ skewPairDiscriminant (1 / 2) U V ≠ 0

/-- A generic pair has an invertible right factor and a characteristic polynomial
whose monic cubic square root has three distinct complex roots. -/
theorem genericSkewPair_cubic (U V : Matrix OrderSixIndices OrderSixIndices ℝ)
    (h : IsGenericSkewPair U V) : (complexify U).det ≠ 0 ∧
      ∃ p : ℂ[X], p.Monic ∧ p.natDegree = 3 ∧ p.roots.Nodup ∧
        p ^ 2 = (complexify V * complexify U).charpoly := by
  classical
  have hmap := skewPairDiscriminant_map Complex.ofRealHom (1 / 2) U V
  have hhalf : Complex.ofRealHom (1 / 2) = (1 / 2 : ℂ) := by rw [map_div₀, map_one, map_ofNat]
  have hδ : Complex.ofRealHom (skewPairDiscriminant (1 / 2) U V) ≠ 0 := Complex.ofReal_ne_zero.mpr h.2.2
  rw [hmap, hhalf] at hδ
  change skewPairDiscriminant (1 / 2) (complexify U) (complexify V) ≠ 0 at hδ
  unfold skewPairDiscriminant at hδ
  have hdet := ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hδ).1).1)
  obtain ⟨p, hmonic, hsq⟩ := charpoly_skew_product_square (complexify U) (complexify V)
    (complexify_skew U h.1) (complexify_skew V h.2.1) hdet
  have hdeg := natDegree_three_of_square_charpoly _ (by simp [OrderSixIndices]) p hsq
  let q := cubicFromSquareCoefficients (1 / 2) (complexify V * complexify U).charpoly
  have hq : q.toPoly = p := by
    change (cubicFromSquareCoefficients (1 / 2) (complexify V * complexify U).charpoly).toPoly = p
    rw [← hsq, cubicFromSquareCoefficients_toPoly p hmonic hdeg]
  have hqa : q.a ≠ 0 := one_ne_zero
  have hqn : (Cubic.map (RingHom.id ℂ) q).roots.Nodup :=
    (Cubic.discr_ne_zero_iff_roots_nodup hqa (IsAlgClosed.splits _)).mp (mul_ne_zero_iff.mp hδ).2
  have hqid : Cubic.map (RingHom.id ℂ) q = q := by ext <;> rfl
  rw [hqid, Cubic.roots, hq] at hqn
  exact ⟨hdet, p, hmonic, hdeg, hqn, hsq⟩

private noncomputable def witnessDiagonal : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, 2, 3]

private noncomputable def witnessU : Matrix OrderSixIndices OrderSixIndices ℝ :=
  fromBlocks 0 witnessDiagonal (-witnessDiagonal) 0

private noncomputable def witnessV : Matrix OrderSixIndices OrderSixIndices ℝ :=
  fromBlocks 0 1 (-1) 0

private theorem witness_product : witnessV * witnessU =
    fromBlocks (-witnessDiagonal) 0 0 (-witnessDiagonal) := by
  simp [witnessU, witnessV, fromBlocks_multiply]

private theorem witnessU_skew : witnessUᵀ = -witnessU := by
  simp [witnessU, witnessDiagonal, fromBlocks_transpose, fromBlocks_neg, diagonal_transpose]

private theorem witnessV_skew : witnessVᵀ = -witnessV := by
  simp [witnessV, fromBlocks_transpose, fromBlocks_neg]

private theorem witness_discriminant_nonzero : skewPairDiscriminant (1 / 2) witnessU witnessV ≠ 0 := by
  let d : Fin 3 → ℝ := ![1, 2, 3]
  have hdiag : -witnessDiagonal = diagonal (fun i => -d i) := diagonal_neg d
  have hdet : (witnessV * witnessU).det ≠ 0 := by
    rw [witness_product, Matrix.det_fromBlocks_zero₁₂, hdiag, Matrix.det_diagonal, Fin.prod_univ_three]
    norm_num [d]
  have hdet' : witnessU.det * witnessV.det ≠ 0 := by
    rwa [mul_comm, ← Matrix.det_mul]
  let p : Cubic ℝ := ⟨1, 6, 11, 6⟩
  have hdeg : p.toPoly.natDegree = 3 := Cubic.natDegree_of_a_ne_zero one_ne_zero
  have hp : p.toPoly.Monic := by
    change p.toPoly.coeff p.toPoly.natDegree = 1
    rw [hdeg, Cubic.coeff_eq_a]
  have hpoly : (witnessV * witnessU).charpoly = p.toPoly ^ 2 := by
    rw [witness_product, Matrix.charpoly_fromBlocks_zero₁₂, hdiag, Matrix.charpoly_diagonal,
      Fin.prod_univ_three, ← pow_two, Cubic.prod_X_sub_C_eq]
    norm_num [d, p]
  have hC : cubicFromSquareCoefficients (1 / 2) (witnessV * witnessU).charpoly = p := by
    apply (Cubic.toPoly_injective _ _).mp
    rw [hpoly, cubicFromSquareCoefficients_toPoly _ hp hdeg]
  rw [skewPairDiscriminant, hC]
  exact mul_ne_zero hdet' (by norm_num [p, Cubic.discr])

private noncomputable def pathMatrix (A W : Matrix OrderSixIndices OrderSixIndices ℝ) :
    Matrix OrderSixIndices OrderSixIndices ℝ[X] :=
  Matrix.of fun i j => (1 - X) * Polynomial.C (A i j) + X * Polynomial.C (W i j)

private theorem pathMatrix_eval (A W : Matrix OrderSixIndices OrderSixIndices ℝ) (t : ℝ) :
    (pathMatrix A W).map (Polynomial.evalRingHom t) = (1 - t) • A + t • W := by
  ext i j
  simp [pathMatrix, Matrix.map_apply, smul_eq_mul]
  exact mul_comm _ _

/-- Every real skew pair is a limit of the generic pairs from the manuscript. -/
theorem skewPair_mem_closure_generic (U V : Matrix OrderSixIndices OrderSixIndices ℝ)
    (hU : Uᵀ = -U) (hV : Vᵀ = -V) :
    (U, V) ∈ closure {p : Matrix OrderSixIndices OrderSixIndices ℝ × Matrix OrderSixIndices OrderSixIndices ℝ |
      IsGenericSkewPair p.1 p.2} := by
  let q : ℝ[X] := skewPairDiscriminant (Polynomial.C (1 / 2))
    (pathMatrix U witnessU) (pathMatrix V witnessV)
  let γ (t : ℝ) := ((1 - t) • U + t • witnessU, (1 - t) • V + t • witnessV)
  have hpath (t : ℝ) : q.eval t = skewPairDiscriminant (1 / 2) (γ t).1 (γ t).2 := by
    change Polynomial.evalRingHom t q = _
    rw [show q = skewPairDiscriminant (Polynomial.C (1 / 2)) _ _ from rfl,
      skewPairDiscriminant_map, pathMatrix_eval, pathMatrix_eval,
      show Polynomial.evalRingHom t (Polynomial.C (1 / 2)) = (1 / 2 : ℝ) from Polynomial.eval_C]
  have hq : q ≠ 0 := by
    intro hz
    have h := hpath 1
    simp only [hz, Polynomial.eval_zero, γ, sub_self, zero_smul, one_smul, zero_add] at h
    exact witness_discriminant_nonzero h.symm
  have h0 : (0 : ℝ) ∈ closure {t : ℝ | q.eval t ≠ 0} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ht, hnot⟩ := (Set.Ioo_infinite hε).exists_notMem_finite (Polynomial.finite_setOfPred_isRoot hq)
    refine ⟨t, hnot, ?_⟩
    simpa [Real.dist_eq, abs_of_pos ht.1, abs_sub_comm] using ht.2
  have hγ : Continuous γ := by unfold γ; fun_prop
  have hsubset : γ '' {t : ℝ | q.eval t ≠ 0} ⊆ {p | IsGenericSkewPair p.1 p.2} := by
    rintro _ ⟨t, ht, rfl⟩
    have hUt : (γ t).1ᵀ = -(γ t).1 := by simp [γ, hU, witnessU_skew, add_comm]
    have hVt : (γ t).2ᵀ = -(γ t).2 := by simp [γ, hV, witnessV_skew, add_comm]
    exact ⟨hUt, hVt, hpath t ▸ ht⟩
  have hlim := closure_mono hsubset (image_closure_subset_closure_image hγ ⟨0, h0, rfl⟩)
  simpa [γ] using hlim

/-- It is enough to construct the adapted unitary bases for generic skew pairs. -/
theorem hasAdaptedBasis_of_generic_adaptedBasis
    (h : ∀ B U V : Matrix OrderSixIndices OrderSixIndices ℝ,
      IsGenericSkewPair U V → HasAdaptedBasis B U V)
    (B U V : Matrix OrderSixIndices OrderSixIndices ℝ)
    (hU : Uᵀ = -U) (hV : Vᵀ = -V) : HasAdaptedBasis B U V :=
  hasAdaptedBasis_of_mem_closure B U V (fun p hp => h B p.1 p.2 hp)
    (skewPair_mem_closure_generic U V hU hV)

end SymmetricMaximizer
