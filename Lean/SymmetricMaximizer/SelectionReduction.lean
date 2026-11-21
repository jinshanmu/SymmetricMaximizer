module

public import SymmetricMaximizer.GenericPairs
public import SymmetricMaximizer.SelectedSubspace
public import SymmetricMaximizer.SelectionProjectivization
public import SymmetricMaximizer.Sharpness
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Reduction to the section-zero assertion

The hypothesis `SelectionSectionHasZero` is the existence of a zero of the three components
on the projective bundle in `lem:selection`. The remaining arguments give the main theorem
from that geometric assertion.
-/

@[expose] public section

open Matrix Module Set Submodule
open scoped Matrix.Norms.Frobenius

namespace SymmetricMaximizer

private theorem realMatrixBilin_alt (A : Matrix OrderSixIndices OrderSixIndices ℝ) (hA : Aᵀ = -A) :
    (realMatrixBilin A).IsAlt := by
  intro x
  rw [realMatrixBilin_apply, ← Matrix.toBilin'_apply']
  exact isAlt_toBilin_of_skew (complexify A) (complexify_skew A hA) x.ofLp

private theorem product_adjoint_bilin (U V : Matrix OrderSixIndices OrderSixIndices ℝ)
    (hU : Uᵀ = -U) (hV : Vᵀ = -V) (x y : OrderSixHermitianSpace) :
    let C := Matrix.toEuclideanLin (complexify V * complexify U)
    realMatrixBilin U (C x) y = realMatrixBilin U x (C y) := by
  dsimp only
  let M := complexify V * complexify U
  rw [realMatrixBilin_apply, realMatrixBilin_apply, Matrix.ofLp_toLpLin, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.toLin'_apply]
  change (M *ᵥ x.ofLp) ⬝ᵥ (complexify U *ᵥ y.ofLp) =
    x.ofLp ⬝ᵥ (complexify U *ᵥ (M *ᵥ y.ofLp))
  have h := skew_product_adjoint (complexify U) (complexify V) (complexify_skew U hU) (complexify_skew V hV)
  change Mᵀ * complexify U = complexify U * M at h
  rw [dotProduct_comm (M *ᵥ x.ofLp), ← Matrix.dotProduct_transpose_mulVec M,
    Matrix.mulVec_mulVec y.ofLp Mᵀ (complexify U), h, ← Matrix.mulVec_mulVec y.ofLp (complexify U) M]

/-- For generic pairs, the section-zero conclusion produces the subspace and the adapted basis. -/
theorem hasAdaptedBasis_of_sectionHasZero (hzero : SelectionSectionHasZero OrderSixHermitianSpace)
    (B U V : Matrix OrderSixIndices OrderSixIndices ℝ) (hgen : IsGenericSkewPair U V) :
    HasAdaptedBasis B U V := by
  classical
  obtain ⟨hdet, p, hp, hd, hroots, hsq⟩ := genericSkewPair_cubic U V hgen
  let M := complexify V * complexify U
  let C : Module.End ℂ OrderSixHermitianSpace := Matrix.toEuclideanLin M
  let F := realMatrixBilin U
  have hF : F.Nondegenerate := realMatrixBilin_nondegenerate U hdet
  have hFalt : F.IsAlt := realMatrixBilin_alt U hgen.1
  have hC : ∀ x y, F (C x) y = F x (C y) := product_adjoint_bilin U V hgen.1 hgen.2.1
  have hchar : C.charpoly = p ^ 2 := by
    let coords := WithLp.linearEquiv 2 ℂ (OrderSixIndices → ℂ)
    change (coords.symm.conj M.toLin').charpoly = p ^ 2
    rw [LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']
    exact hsq.symm
  obtain ⟨root, hroot, hdim, hsum⟩ := exists_three_maxGenEigenspaces C p hp hd hroots hchar
  let E (i : Fin 3) := C.maxGenEigenspace (root i)
  have hindep : iSupIndep E := C.independent_maxGenEigenspace.comp hroot
  have hscalar (i : Fin 3) : ∃ c : ℂ, ∀ x ∈ E i, C x = c • x := by
    have hinvariant : Set.MapsTo C (E i) (E i) :=
      Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl C) (root i)
    obtain ⟨c, hc⟩ := eq_smul_one_of_alternating_finrank_two (hdim i) (F.restrict (E i))
      (fun x => hFalt x) (nondegenerate_maxGenEigenspace F hF C hC (root i))
      (C.restrict hinvariant) (fun x y => hC x y)
    refine ⟨c, fun x hx => ?_⟩
    exact congrArg (fun T : Module.End ℂ (E i) => (T ⟨x, hx⟩ : OrderSixHermitianSpace)) hc
  let Bmap : Module.End ℂ OrderSixHermitianSpace := Matrix.toEuclideanLin (complexify B)
  have hValt : (realMatrixBilin V).IsAlt := realMatrixBilin_alt V hgen.2.1
  obtain ⟨z, hz⟩ :=
    hzero E hindep hsum hdim Bmap (realMatrixBilin V) F hValt hFalt
  obtain ⟨hker, hα, hβ⟩ :=
    (selectionSectionValue_eq_zero_iff Bmap (realMatrixBilin V) F hValt hFalt z).mp hz
  let L := selectionPlane z.val.1
  let v (i : Fin 3) : OrderSixHermitianSpace := (z.val.1 i).rep
  have hv (i : Fin 3) : v i ∈ E i := (z.val.1 i).rep.property
  have hspan : L = Submodule.span ℂ (Set.range v) := selectionPlane_eq_span z.val.1
  have hL : finrank ℂ L = 3 := finrank_selectionPlane hindep z.val.1
  have hpair (i j : Fin 3) : F (v i) (v j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact hFalt _
    · exact alternating_orthogonal_maxGenEigenspace F C hC (fun he => hij (hroot he)) (hv i) (hv j)
  have hIso : ∀ x ∈ L, ∀ y ∈ L, F x y = 0 := by
    have hleft (i : Fin 3) : L ≤ LinearMap.ker (F (v i)) := by
      rw [hspan]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact LinearMap.mem_ker.mpr (hpair i j)
    intro x hx y hy
    have hright : L ≤ LinearMap.ker (LinearMap.flip F y) := by
      rw [hspan]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hleft i hy
    exact LinearMap.mem_ker.mp (hright hx)
  have hstable : ∀ x ∈ L, C x ∈ L := by
    change L ≤ L.comap C
    conv_lhs => rw [hspan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := hscalar i
    change C (v i) ∈ L
    rw [hc (v i) (hv i)]
    apply L.smul_mem
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨hrank, hV, hU⟩ := selection_conclusions_of_section_zero Bmap (realMatrixBilin V) F
    L (selectionLine z) hL (finrank_selectionLine z) hker hα hβ
  exact hasAdaptedBasis_of_selectedSubspace B U V hgen.1 hgen.2.1 hdet L hL hIso hstable hrank hV hU

/-- The manuscript's universal norm inequality follows from the section-zero assertion
exactly in orders at most six. -/
theorem all_orders_of_sectionHasZero (hzero : SelectionSectionHasZero OrderSixHermitianSpace)
    (n : ℕ) :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, skewNorm A ≤ symmetricNorm A) ↔ n ≤ 6 := by
  constructor
  · intro h
    by_contra! hn
    obtain ⟨A, hgap⟩ := exists_strict_gap (by omega : 7 ≤ n)
    exact (not_lt_of_ge (h A) hgap)
  · intro hn A
    refine skewNorm_le_symmetricNorm_of_order_six (fun A₆ => ?_) hn A
    let e : OrderSixIndices ≃ Fin 6 := finSumFinEquiv
    have h := skewNorm_le_symmetricNorm_of_adaptedBasis
      (hasAdaptedBasis_of_generic_adaptedBasis (hasAdaptedBasis_of_sectionHasZero hzero))
      (reindex e.symm e.symm A₆)
    unfold symmetricNorm skewNorm at h
    rw [restricted_opNorm_reindex, restricted_opNorm_reindex] at h
    exact h

end SymmetricMaximizer
