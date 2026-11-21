module

public import SymmetricMaximizer.OrderSix
public import SymmetricMaximizer.Selection
public import SymmetricMaximizer.SingularBases
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

/-!
# Constructing the adapted unitary basis from the selected subspace

An isotropic three-plane invariant under `VU`, with the compression and form restrictions
from `lem:selection`, supplies the unitary blocks in `lem:unitary`.
-/

@[expose] public section

open Matrix Module Submodule
open scoped InnerProductSpace

namespace SymmetricMaximizer

/-- The standard six-dimensional Hermitian space for the selection lemma. -/
abbrev OrderSixHermitianSpace := EuclideanSpace ℂ OrderSixIndices

/-- The complex bilinear form `xᵀ A y` of a real coefficient matrix in the standard coordinates. -/
noncomputable def realMatrixBilin (A : Matrix OrderSixIndices OrderSixIndices ℝ) :
    LinearMap.BilinForm ℂ OrderSixHermitianSpace :=
  LinearMap.BilinForm.congr (WithLp.linearEquiv 2 ℂ (OrderSixIndices → ℂ)).symm
    (Matrix.toBilin' (complexify A))

theorem realMatrixBilin_apply (A : Matrix OrderSixIndices OrderSixIndices ℝ)
    (x y : OrderSixHermitianSpace) :
    realMatrixBilin A x y = x.ofLp ⬝ᵥ (complexify A *ᵥ y.ofLp) := by
  change Matrix.toBilin' (complexify A) x.ofLp y.ofLp = _
  exact Matrix.toBilin'_apply' _ _ _

theorem realMatrixBilin_nondegenerate (A : Matrix OrderSixIndices OrderSixIndices ℝ)
    (hdet : (complexify A).det ≠ 0) : (realMatrixBilin A).Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet).congr _

private def conjugateVector (x : OrderSixHermitianSpace) : OrderSixHermitianSpace :=
  WithLp.toLp 2 (star x.ofLp)

private def columnMatrix (e : OrderSixIndices → OrderSixHermitianSpace) :
    Matrix OrderSixIndices OrderSixIndices ℂ := Matrix.of fun i j => (e j).ofLp i

private theorem column_inner (e f : OrderSixIndices → OrderSixHermitianSpace) (i j : OrderSixIndices) :
    ((columnMatrix e)ᴴ * columnMatrix f) i j = inner ℂ (e i) (f j) := by
  simp [columnMatrix, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

private theorem mul_columnMatrix (A : Matrix OrderSixIndices OrderSixIndices ℂ)
    (e : OrderSixIndices → OrderSixHermitianSpace) :
    A * columnMatrix e = columnMatrix (fun i => Matrix.toEuclideanLin A (e i)) := by
  ext i j
  simp [columnMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem similarity_entry (A : Matrix OrderSixIndices OrderSixIndices ℂ)
    (e : OrderSixIndices → OrderSixHermitianSpace) (i j : OrderSixIndices) :
    unitarySimilarity (columnMatrix e) A i j = inner ℂ (e i) (Matrix.toEuclideanLin A (e j)) := by
  rw [unitarySimilarity, Matrix.mul_assoc, mul_columnMatrix, column_inner]

private theorem congruence_entry (A : Matrix OrderSixIndices OrderSixIndices ℂ)
    (e : OrderSixIndices → OrderSixHermitianSpace) (i j : OrderSixIndices) :
    unitaryCongruence (columnMatrix e) A i j =
      inner ℂ (e i) (Matrix.toEuclideanLin A (conjugateVector (e j))) := by
  have h : (columnMatrix e)ᴴᵀ = columnMatrix (fun k => conjugateVector (e k)) := rfl
  rw [unitaryCongruence, Matrix.mul_assoc, h, mul_columnMatrix, column_inner]

private theorem congruence_entry_real (A : Matrix OrderSixIndices OrderSixIndices ℝ)
    (e : OrderSixIndices → OrderSixHermitianSpace) (i j : OrderSixIndices) :
    unitaryCongruence (columnMatrix e) (complexify A) i j = star (realMatrixBilin A (e i) (e j)) := by
  have h (v : OrderSixIndices → ℂ) : star (complexify A *ᵥ v) = complexify A *ᵥ star v := by
    rw [Matrix.star_mulVec, ← complexify_transpose_eq_adjoint, complexify_transpose,
      ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
  rw [congruence_entry, realMatrixBilin_apply, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin]
  change (complexify A *ᵥ star (e j).ofLp) ⬝ᵥ star (e i).ofLp = _
  rw [← h, star_dotProduct_star]

private theorem congruence_skew (E : Matrix OrderSixIndices OrderSixIndices ℂ)
    (A : Matrix OrderSixIndices OrderSixIndices ℝ) (hA : Aᵀ = -A) :
    (unitaryCongruence E (complexify A))ᵀ = -unitaryCongruence E (complexify A) := by
  have h : (complexify A)ᵀ = (-1 : ℂ) • complexify A := by
    rw [← complexify_transpose, hA, ← neg_one_smul ℝ A, complexify_smul]
    simp
  rw [unitaryCongruence_transpose, h, unitaryCongruence_smul, neg_one_smul]

private theorem maps_conjugate_complement (U V : Matrix OrderSixIndices OrderSixIndices ℝ)
    (hdet : (complexify U).det ≠ 0) (L : Submodule ℂ OrderSixHermitianSpace)
    (hL : finrank ℂ L = 3) (hIso : ∀ x ∈ L, ∀ y ∈ L, realMatrixBilin U x y = 0)
    (hstable : ∀ x ∈ L, Matrix.toEuclideanLin (complexify V * complexify U) x ∈ L)
    (w : OrderSixHermitianSpace) (hw : w ∈ Lᗮ) :
    Matrix.toEuclideanLin (complexify V) (conjugateVector w) ∈ L := by
  let F := realMatrixBilin U
  have hF : F.Nondegenerate := realMatrixBilin_nondegenerate U hdet
  have hLe : L ≤ F.orthogonal L := fun _ hy => LinearMap.BilinForm.mem_orthogonal_iff.mpr
    fun x hx => hIso x hx _ hy
  have hdim : finrank ℂ (F.orthogonal L) = 3 := by
    rw [F.finrank_orthogonal hF, hL]
    simp [OrderSixHermitianSpace, OrderSixIndices]
  have hcomp : L = F.orthogonal L := Submodule.eq_of_le_of_finrank_le hLe (hdim.trans hL.symm).le
  let Umap := Matrix.toEuclideanLin (complexify U)
  have hUinj : Function.Injective Umap := by
    intro x y hxy
    apply WithLp.ofLp_injective
    apply Matrix.mulVec_injective_of_det_ne_zero hdet
    exact congrArg WithLp.ofLp hxy
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hUinj) (conjugateVector w)
  have hxmem : x ∈ L := by
    rw [hcomp]
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun y hy => ?_
    have h : complexify U *ᵥ x.ofLp = star w.ofLp := congrArg WithLp.ofLp hx
    have hi := (L.mem_orthogonal w).mp hw y hy
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
    change realMatrixBilin U y x = 0
    rw [realMatrixBilin_apply, h, dotProduct_star, hi, star_zero]
  have hact : Matrix.toEuclideanLin (complexify V * complexify U) x =
      Matrix.toEuclideanLin (complexify V) (Umap x) := by
    apply WithLp.ofLp_injective
    simp [Umap, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  have h := hstable x hxmem
  rw [hact, hx] at h
  exact h

/-- The three-plane and its compression from `lem:selection` give the adapted basis. -/
theorem hasAdaptedBasis_of_selectedSubspace (B U V : Matrix OrderSixIndices OrderSixIndices ℝ)
    (hU : Uᵀ = -U) (hV : Vᵀ = -V) (hdet : (complexify U).det ≠ 0)
    (L : Submodule ℂ OrderSixHermitianSpace) (hL : finrank ℂ L = 3)
    (hIso : ∀ x ∈ L, ∀ y ∈ L, realMatrixBilin U x y = 0)
    (hstable : ∀ x ∈ L, Matrix.toEuclideanLin (complexify V * complexify U) x ∈ L) :
    let g := compression (Matrix.toEuclideanLin (complexify B)) L
    let K : Submodule ℂ L := LinearMap.ker g
    let H := Submodule.orthogonal (𝕜 := ℂ) (E := L) K
    finrank ℂ (LinearMap.range g) ≤ 2 →
    (∀ x ∈ H, ∀ y ∈ H,
      realMatrixBilin V (x : OrderSixHermitianSpace) (y : OrderSixHermitianSpace) = 0) →
    (∀ x : Lᗮ, x ∈ LinearMap.range g → ∀ y : Lᗮ, y ∈ LinearMap.range g →
      realMatrixBilin U (x : OrderSixHermitianSpace) (y : OrderSixHermitianSpace) = 0) →
    HasAdaptedBasis B U V := by
  dsimp only
  intro hrank hα hβ
  let Bmap := Matrix.toEuclideanLin (complexify B)
  let g := compression Bmap L
  have hLp : finrank ℂ Lᗮ = 3 := by
    have h := L.finrank_add_finrank_orthogonal
    rw [hL] at h
    have hdim : finrank ℂ OrderSixHermitianSpace = 6 := by simp [OrderSixHermitianSpace, OrderSixIndices]
    omega
  obtain ⟨v, w, s, hs_nonneg, hs_antitone, hs_zero, hsingular, hsupp⟩ :=
    exists_singular_bases (E := L) (F := Lᗮ) g hL hLp
  let e : OrderSixIndices → OrderSixHermitianSpace := Sum.elim (fun i => (v i : OrderSixHermitianSpace))
    (fun i => (w i : OrderSixHermitianSpace))
  let E := columnMatrix e
  have hE : E ∈ Matrix.unitaryGroup OrderSixIndices ℂ := Matrix.mem_unitaryGroup_iff'.mpr (by
    change Eᴴ * E = 1
    ext i j
    rw [column_inner, Matrix.one_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa [e] using (orthonormal_iff_ite.mp v.orthonormal i j)
    · simp [e, (L.mem_orthogonal (w j)).mp (w j).property (v i) (v i).property]
    · simp [e, L.inner_left_of_mem_orthogonal (v j).property (w i).property]
    · simpa [e] using (orthonormal_iff_ite.mp w.orthonormal i j))
  let Bhat := unitarySimilarity E (complexify B)
  let Uhat := unitaryCongruence E (complexify U)
  let Vhat := unitaryCongruence E (complexify V)
  have hG : Bhat.toBlocks₂₁ = diagonal (fun i : Fin 3 => (s i : ℂ)) := by
    ext i j
    change unitarySimilarity (columnMatrix e) (complexify B) (Sum.inr i) (Sum.inl j) = _
    rw [similarity_entry]
    change inner ℂ (w i : OrderSixHermitianSpace) (Bmap (v j : OrderSixHermitianSpace)) = _
    rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    change inner ℂ (w i) (g (v j)) = _
    rw [hsingular j, inner_smul_right, orthonormal_iff_ite.mp w.orthonormal]
    by_cases hij : i = j <;> simp [hij]
  have hU₁₁ : Uhat.toBlocks₁₁ = 0 := by
    ext i j
    change unitaryCongruence (columnMatrix e) (complexify U) (Sum.inl i) (Sum.inl j) = 0
    rw [congruence_entry_real]
    simp [e, hIso (v i) (v i).property (v j) (v j).property]
  have hV₂₂ : Vhat.toBlocks₂₂ = 0 := by
    ext i j
    change unitaryCongruence (columnMatrix e) (complexify V) (Sum.inr i) (Sum.inr j) = 0
    rw [congruence_entry]
    exact L.inner_left_of_mem_orthogonal
      (maps_conjugate_complement U V hdet L hL hIso hstable _ (w j).property) (w i).property
  have hU₂₁ : Uhat.toBlocks₂₁ = -Uhat.toBlocks₁₂ᵀ := by
    ext i j
    exact congrArg (fun A : Matrix OrderSixIndices OrderSixIndices ℂ => A (Sum.inl j) (Sum.inr i))
      (congruence_skew E U hU)
  have hV₂₁ : Vhat.toBlocks₂₁ = -Vhat.toBlocks₁₂ᵀ := by
    ext i j
    exact congrArg (fun A : Matrix OrderSixIndices OrderSixIndices ℂ => A (Sum.inl j) (Sum.inr i))
      (congruence_skew E V hV)
  refine ⟨E, hE, ⟨{
    B₁₁ := Bhat.toBlocks₁₁
    B₁₂ := Bhat.toBlocks₁₂
    B₂₂ := Bhat.toBlocks₂₂
    X := Uhat.toBlocks₁₂
    Y := Vhat.toBlocks₁₂
    U₂₂ := Uhat.toBlocks₂₂
    V₁₁ := Vhat.toBlocks₁₁
    g := fun i => s i
    g_nonneg := fun i => hs_nonneg i
    g_antitone := fun _ _ hij => hs_antitone hij
    g_last_zero := hs_zero 2 hrank
    coefficient_eq := ?_
    left_eq := ?_
    right_eq := ?_
    leading_left_zero := ?_
    leading_right_zero := ?_ }⟩⟩
  · change Bhat = _
    conv_lhs => rw [← fromBlocks_toBlocks Bhat, hG]
  · change Uhat = _
    conv_lhs => rw [← fromBlocks_toBlocks Uhat, hU₁₁, hU₂₁]
  · change Vhat = _
    conv_lhs => rw [← fromBlocks_toBlocks Vhat, hV₂₂, hV₂₁]
  · intro i j hi hj
    change unitaryCongruence (columnMatrix e) (complexify U) (Sum.inr i) (Sum.inr j) = 0
    rw [congruence_entry_real]
    simp [e, hβ (w i) (hsupp i hi).2 (w j) (hsupp j hj).2]
  · intro i j hi hj
    change unitaryCongruence (columnMatrix e) (complexify V) (Sum.inl i) (Sum.inl j) = 0
    rw [congruence_entry_real]
    simp [e, hα (v i) (hsupp i hi).1 (v j) (hsupp j hj).1]

end SymmetricMaximizer
