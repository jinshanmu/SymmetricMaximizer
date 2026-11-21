module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

/-!
# Generalized eigenspaces of an operator self-adjoint for an alternating form

The first paragraph of `lem:unitary` proves that the characteristic polynomial is a square.
-/

public section

open Matrix Module Polynomial
open scoped BigOperators

namespace SymmetricMaximizer

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- Distinct generalized eigenspaces are orthogonal for a bilinear form for which the
operator is self-adjoint. -/
theorem alternating_orthogonal_maxGenEigenspace [FiniteDimensional K W]
    (F : LinearMap.BilinForm K W) (C : Module.End K W) (hC : ∀ x y, F (C x) y = F x (C y))
    {μ ν : K} (hμν : μ ≠ ν) {x y : W} (hx : x ∈ C.maxGenEigenspace μ)
    (hy : y ∈ C.maxGenEigenspace ν) : F x y = 0 := by
  let D := C - μ • (1 : Module.End K W)
  have hD (a b : W) : F (D a) b = F a (D b) := by
    simp [D, LinearMap.sub_apply, LinearMap.smul_apply, hC a b]
  have hpow (k : ℕ) (a b : W) : F ((D ^ k) a) b = F a ((D ^ k) b) := by
    induction k generalizing a b with
    | zero => simp
    | succ k ih =>
      calc
        F ((D ^ (k + 1)) a) b = F ((D ^ k) (D a)) b := by rw [pow_succ, mul_apply_eq_comp]
        _ = F (D a) ((D ^ k) b) := ih _ _
        _ = F a (D ((D ^ k) b)) := hD _ _
        _ = F a ((D ^ (k + 1)) b) := by rw [pow_succ', mul_apply_eq_comp]
  obtain ⟨k, hkill⟩ := (C.mem_maxGenEigenspace μ x).mp hx
  have hcomm : Commute C (D ^ k) := by
    change C * D ^ k = D ^ k * C
    simpa only [D, Algebra.algebraMap_eq_smul_one] using Algebra.mul_sub_algebraMap_pow_commutes C μ k
  let T := (D ^ k).restrict (Module.End.mapsTo_maxGenEigenspace_of_comm hcomm ν)
  have hT : Function.Injective T := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro z hz
    apply Subtype.ext
    have hkillz : ((D ^ k) (z : W)) = 0 := congrArg Subtype.val hz
    have hzμ : (z : W) ∈ C.maxGenEigenspace μ :=
      (C.mem_maxGenEigenspace μ z).mpr ⟨k, hkillz⟩
    have hzboth : (z : W) ∈ C.maxGenEigenspace μ ⊓ C.maxGenEigenspace ν := ⟨hzμ, z.property⟩
    rw [(C.disjoint_genEigenspace hμν ⊤ ⊤).eq_bot] at hzboth
    exact hzboth))
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hT) ⟨y, hy⟩
  have hz' : ((D ^ k) (z : W)) = y := congrArg Subtype.val hz
  rw [← hz', ← hpow k]
  change F (((C - μ • (1 : Module.End K W)) ^ k) x) (z : W) = 0
  rw [hkill, map_zero, LinearMap.zero_apply]

theorem nondegenerate_maxGenEigenspace [FiniteDimensional K W] [IsAlgClosed K]
    (F : LinearMap.BilinForm K W) (hF : F.Nondegenerate) (C : Module.End K W)
    (hC : ∀ x y, F (C x) y = F x (C y)) (μ : K) :
    (F.restrict (C.maxGenEigenspace μ)).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  have hspan : (⊤ : Submodule K W) ≤ LinearMap.ker (F (x : W)) := by
    rw [← C.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun ν y hy => LinearMap.mem_ker.mpr ?_
    by_cases h : μ = ν
    · subst ν
      exact hx ⟨y, hy⟩
    · exact alternating_orthogonal_maxGenEigenspace F C hC h x.property hy
  exact Subtype.ext (hF.1 (x : W) fun y => LinearMap.mem_ker.mp (hspan (Submodule.mem_top : y ∈ ⊤)))

/-- A nondegenerate alternating form over a characteristic-zero field has even dimension. -/
theorem even_finrank_of_alternating [CharZero K] [FiniteDimensional K W]
    (F : LinearMap.BilinForm K W) (hAlt : F.IsAlt) (hF : F.Nondegenerate) : Even (finrank K W) := by
  let b := Module.finBasis K W
  let M := LinearMap.BilinForm.toMatrix b F
  have hdet : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hF
  have hM : Mᵀ = -M := by
    ext i j
    simp only [M, Matrix.transpose_apply, Matrix.neg_apply, LinearMap.BilinForm.toMatrix_apply]
    exact (hAlt.neg_eq (b i) (b j)).symm
  rcases Nat.even_or_odd (finrank K W) with h | h
  · exact h
  · have hd := congrArg Matrix.det hM
    rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin, h.neg_one_pow] at hd
    exact (hdet (by linear_combination (1 / 2 : K) * hd)).elim

/-- Self-adjointness for a nondegenerate alternating form makes every root multiplicity even. -/
theorem even_charpoly_rootMultiplicity [CharZero K] [FiniteDimensional K W] [IsAlgClosed K]
    (F : LinearMap.BilinForm K W) (hAlt : F.IsAlt) (hF : F.Nondegenerate) (C : Module.End K W)
    (hC : ∀ x y, F (C x) y = F x (C y)) (μ : K) : Even (C.charpoly.rootMultiplicity μ) := by
  rw [← C.finrank_maxGenEigenspace_eq μ]
  exact even_finrank_of_alternating _ (fun x => hAlt x) (nondegenerate_maxGenEigenspace F hF C hC μ)

/-- The characteristic polynomial is a square, with the monic square root obtained by
halving the multiplicities in its linear factorization. -/
theorem charpoly_eq_square_of_alternating [CharZero K] [FiniteDimensional K W] [IsAlgClosed K]
    (F : LinearMap.BilinForm K W) (hAlt : F.IsAlt) (hF : F.Nondegenerate) (C : Module.End K W)
    (hC : ∀ x y, F (C x) y = F x (C y)) : ∃ p : K[X], p.Monic ∧ p ^ 2 = C.charpoly := by
  classical
  let roots := C.charpoly.roots.toFinset
  let m : K → ℕ := fun a => C.charpoly.rootMultiplicity a / 2
  let p : K[X] := ∏ a ∈ roots, (X - Polynomial.C a) ^ m a
  have hp : p.Monic := monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow _
  have hfactor : C.charpoly = ∏ a ∈ roots, (X - Polynomial.C a) ^ C.charpoly.rootMultiplicity a := by
    have hsplit : C.charpoly.Splits := IsAlgClosed.splits _
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic C.charpoly_monic, Finset.prod_multiset_map_count]
    simp [roots, count_roots]
  refine ⟨p, hp, ?_⟩
  change (∏ a ∈ roots, (X - Polynomial.C a) ^ m a) ^ 2 = C.charpoly
  rw [hfactor, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  rcases even_charpoly_rootMultiplicity F hAlt hF C hC a with ⟨d, hd⟩
  rw [← pow_mul, show m a * 2 = C.charpoly.rootMultiplicity a by dsimp [m]; omega]

/-- On a two-dimensional space, self-adjointness for a nondegenerate alternating form
forces the operator to be scalar. -/
theorem eq_smul_one_of_alternating_finrank_two [CharZero K] [FiniteDimensional K W]
    (hW : finrank K W = 2) (F : LinearMap.BilinForm K W) (hAlt : F.IsAlt) (hF : F.Nondegenerate)
    (C : Module.End K W) (hC : ∀ x y, F (C x) y = F x (C y)) : ∃ c : K, C = c • 1 := by
  let b := Module.finBasisOfFinrankEq K W hW
  let J := LinearMap.BilinForm.toMatrix b F
  let M := LinearMap.toMatrix b b C
  have h₀₀ : J 0 0 = 0 := (LinearMap.BilinForm.toMatrix_apply b F _ _).trans (hAlt _)
  have h₁₁ : J 1 1 = 0 := (LinearMap.BilinForm.toMatrix_apply b F _ _).trans (hAlt _)
  have h₁₀ : J 1 0 = -J 0 1 := by
    simp only [J, LinearMap.BilinForm.toMatrix_apply]
    exact (hAlt.neg_eq (b 0) (b 1)).symm
  have hne : J 0 1 ≠ 0 := by
    intro h
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hF
    change J.det = 0
    rw [Matrix.det_fin_two, h₀₀, h₁₁, h]
    simp
  have hM : Mᵀ * J = J * M := by
    have h : F.compLeft C = F.compRight C := by
      ext x y
      exact hC x y
    change (LinearMap.toMatrix b b C)ᵀ * LinearMap.BilinForm.toMatrix b F =
      LinearMap.BilinForm.toMatrix b F * LinearMap.toMatrix b b C
    rw [← LinearMap.BilinForm.toMatrix_compLeft, ← LinearMap.BilinForm.toMatrix_compRight, h]
  have h_off₁₀ : M 1 0 = 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) hM
    simp [Matrix.mul_apply, Fin.sum_univ_two, h₀₀, h₁₀] at h
    have hproduct : M 1 0 * J 0 1 = 0 := by linear_combination -(1 / 2 : K) * h
    exact (mul_eq_zero.mp hproduct).resolve_right hne
  have h_off₀₁ : M 0 1 = 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 1) hM
    simp [Matrix.mul_apply, Fin.sum_univ_two, h₁₁, h₁₀] at h
    have hproduct : M 0 1 * J 0 1 = 0 := by linear_combination (1 / 2 : K) * h
    exact (mul_eq_zero.mp hproduct).resolve_right hne
  have h_diag : M 1 1 = M 0 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hM
    simp [Matrix.mul_apply, Fin.sum_univ_two, h₀₀, h₁₁] at h
    exact (mul_left_cancel₀ hne ((mul_comm (M 0 0) (J 0 1)).symm.trans h)).symm
  refine ⟨M 0 0, (LinearMap.toMatrix b b).injective ?_⟩
  rw [map_smul, LinearMap.toMatrix_one]
  change M = M 0 0 • 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, h_off₁₀, h_off₀₁, h_diag]

/-- A square of a split monic cubic with distinct roots gives three generalized eigenspaces,
each of dimension two, forming a direct sum of the whole space. -/
theorem exists_three_maxGenEigenspaces [FiniteDimensional K W] [IsAlgClosed K]
    (C : Module.End K W) (p : K[X]) (hmonic : p.Monic) (hdeg : p.natDegree = 3)
    (hnodup : p.roots.Nodup) (hchar : C.charpoly = p ^ 2) :
    ∃ root : Fin 3 → K, Function.Injective root ∧
      (∀ i, finrank K (C.maxGenEigenspace (root i)) = 2) ∧
      (⨆ i, C.maxGenEigenspace (root i)) = ⊤ := by
  classical
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.toFinset.card = 3 := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots, hdeg]
  let index : ↥p.roots.toFinset ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hcard)
  let root (i : Fin 3) := (index.symm i).val
  have hr (i : Fin 3) : root i ∈ p.roots := Multiset.mem_toFinset.mp (index.symm i).property
  have hrange {z : K} (hz : z ∈ p.roots) : ∃ i, root i = z := by
    refine ⟨index ⟨z, Multiset.mem_toFinset.mpr hz⟩, ?_⟩
    simp [root]
  have hm (z : K) : finrank K (C.maxGenEigenspace z) = p.roots.count z + p.roots.count z := by
    rw [C.finrank_maxGenEigenspace_eq, hchar, pow_two,
      rootMultiplicity_mul (mul_ne_zero hmonic.ne_zero hmonic.ne_zero), count_roots]
  refine ⟨root, Subtype.val_injective.comp index.symm.injective, ?_, ?_⟩
  · intro i
    rw [hm, Multiset.count_eq_one_of_mem hnodup (hr i)]
  · apply top_unique
    rw [← C.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun z => ?_
    by_cases hz : z ∈ p.roots
    · obtain ⟨i, rfl⟩ := hrange hz
      exact le_iSup (fun j => C.maxGenEigenspace (root j)) i
    · have h0 : finrank K (C.maxGenEigenspace z) = 0 := by
        rw [hm, Multiset.count_eq_zero_of_notMem hz, add_zero]
      rw [Submodule.finrank_eq_zero.mp h0]
      exact bot_le

end SymmetricMaximizer
