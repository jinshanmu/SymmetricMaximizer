module

public import SymmetricMaximizer.OrderSix
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

/-!
# Passing to a limiting adapted unitary basis

This is the compactness step at the end of `lem:unitary`. The leading blocks are
encoded by multiplying their entries by the two corresponding singular values.
-/

public section

open Matrix Set

namespace SymmetricMaximizer

private abbrev ComplexMatrix := Matrix OrderSixIndices OrderSixIndices ℂ
private abbrev RealMatrix := Matrix OrderSixIndices OrderSixIndices ℝ

private noncomputable def observedDiagonal (B : ComplexMatrix) (i : Fin 3) : ℝ :=
  (B.toBlocks₂₁ i i).re

private def adaptedEquations (B U V : ComplexMatrix) : Prop :=
  let g := observedDiagonal B
  U.toBlocks₁₁ = 0 ∧ V.toBlocks₂₂ = 0 ∧
  U.toBlocks₂₁ = -U.toBlocks₁₂ᵀ ∧ V.toBlocks₂₁ = -V.toBlocks₁₂ᵀ ∧
  B.toBlocks₂₁ = diagonal (fun i => (g i : ℂ)) ∧
  (∀ i, 0 ≤ g i) ∧ Antitone g ∧ g 2 = 0 ∧
  (∀ i j, (g i : ℂ) * (g j : ℂ) * U.toBlocks₂₂ i j = 0) ∧
  (∀ i j, (g i : ℂ) * (g j : ℂ) * V.toBlocks₁₁ i j = 0)

private theorem zero_if_supported (g : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (∀ i j, (g i : ℂ) * (g j : ℂ) * M i j = 0) ↔
      ∀ i j, g i ≠ 0 → g j ≠ 0 → M i j = 0 := by
  constructor
  · intro h i j hi hj
    exact (mul_eq_zero.mp (h i j)).resolve_left
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hi) (Complex.ofReal_ne_zero.mpr hj))
  · intro h i j
    by_cases hi : g i = 0
    · simp [hi]
    by_cases hj : g j = 0
    · simp [hj]
    · simp [h i j hi hj]

private theorem adapted_iff_equations (B U V : ComplexMatrix) :
    Nonempty (AdaptedBlockForm B U V) ↔ adaptedEquations B U V := by
  constructor
  · rintro ⟨a⟩
    have hg : observedDiagonal B = a.g := by
      funext i
      simp [observedDiagonal, a.coefficient_eq]
    have hU₁₁ : U.toBlocks₁₁ = 0 := congrArg Matrix.toBlocks₁₁ a.left_eq
    have hV₂₂ : V.toBlocks₂₂ = 0 := congrArg Matrix.toBlocks₂₂ a.right_eq
    have hU₂₁ : U.toBlocks₂₁ = -U.toBlocks₁₂ᵀ := by rw [a.left_eq]; rfl
    have hV₂₁ : V.toBlocks₂₁ = -V.toBlocks₁₂ᵀ := by rw [a.right_eq]; rfl
    have hB₂₁ : B.toBlocks₂₁ = diagonal (fun i => (a.g i : ℂ)) := congrArg Matrix.toBlocks₂₁ a.coefficient_eq
    have hU₂₂ : U.toBlocks₂₂ = a.U₂₂ := congrArg Matrix.toBlocks₂₂ a.left_eq
    have hV₁₁ : V.toBlocks₁₁ = a.V₁₁ := congrArg Matrix.toBlocks₁₁ a.right_eq
    dsimp only [adaptedEquations]
    rw [hg, hU₂₂, hV₁₁, zero_if_supported, zero_if_supported]
    exact ⟨hU₁₁, hV₂₂, hU₂₁, hV₂₁, hB₂₁, a.g_nonneg, a.g_antitone, a.g_last_zero,
      a.leading_left_zero, a.leading_right_zero⟩
  · rintro ⟨hU₁₁, hV₂₂, hU₂₁, hV₂₁, hB₂₁, hnonneg, horder, hlast, hU₂₂, hV₁₁⟩
    refine ⟨{
      B₁₁ := B.toBlocks₁₁
      B₁₂ := B.toBlocks₁₂
      B₂₂ := B.toBlocks₂₂
      X := U.toBlocks₁₂
      Y := V.toBlocks₁₂
      U₂₂ := U.toBlocks₂₂
      V₁₁ := V.toBlocks₁₁
      g := observedDiagonal B
      g_nonneg := hnonneg
      g_antitone := horder
      g_last_zero := hlast
      coefficient_eq := ?_
      left_eq := ?_
      right_eq := ?_
      leading_left_zero := (zero_if_supported _ _).mp hU₂₂
      leading_right_zero := (zero_if_supported _ _).mp hV₁₁ }⟩
    · conv_lhs => rw [← fromBlocks_toBlocks B, hB₂₁]
    · conv_lhs => rw [← fromBlocks_toBlocks U, hU₁₁, hU₂₁]
    · conv_lhs => rw [← fromBlocks_toBlocks V, hV₂₂, hV₂₁]

@[fun_prop] private theorem continuous_complexify {T : Type*} [TopologicalSpace T]
    {f : T → RealMatrix} (hf : Continuous f) :
    Continuous (fun x => complexify (f x)) := hf.matrix_map Complex.continuous_ofReal

private theorem isClosed_adaptedForm : IsClosed {p : ComplexMatrix × ComplexMatrix × ComplexMatrix |
    Nonempty (AdaptedBlockForm p.1 p.2.1 p.2.2)} := by
  let P := ComplexMatrix × ComplexMatrix × ComplexMatrix
  have hB : Continuous (fun p : P => p.1) := continuous_fst
  have hU : Continuous (fun p : P => p.2.1) := continuous_fst.comp continuous_snd
  have hV : Continuous (fun p : P => p.2.2) := continuous_snd.comp continuous_snd
  have hB₂₁ : Continuous (fun p : P => p.1.toBlocks₂₁) := hB.matrix_submatrix Sum.inr Sum.inl
  have hU₁₁ : Continuous (fun p : P => p.2.1.toBlocks₁₁) := hU.matrix_submatrix Sum.inl Sum.inl
  have hU₁₂ : Continuous (fun p : P => p.2.1.toBlocks₁₂) := hU.matrix_submatrix Sum.inl Sum.inr
  have hU₂₁ : Continuous (fun p : P => p.2.1.toBlocks₂₁) := hU.matrix_submatrix Sum.inr Sum.inl
  have hU₂₂ : Continuous (fun p : P => p.2.1.toBlocks₂₂) := hU.matrix_submatrix Sum.inr Sum.inr
  have hV₁₁ : Continuous (fun p : P => p.2.2.toBlocks₁₁) := hV.matrix_submatrix Sum.inl Sum.inl
  have hV₁₂ : Continuous (fun p : P => p.2.2.toBlocks₁₂) := hV.matrix_submatrix Sum.inl Sum.inr
  have hV₂₁ : Continuous (fun p : P => p.2.2.toBlocks₂₁) := hV.matrix_submatrix Sum.inr Sum.inl
  have hV₂₂ : Continuous (fun p : P => p.2.2.toBlocks₂₂) := hV.matrix_submatrix Sum.inr Sum.inr
  have hg (i : Fin 3) : Continuous (fun p : P => observedDiagonal p.1 i) :=
    Complex.continuous_re.comp (hB₂₁.matrix_elem i i)
  have hgC (i : Fin 3) : Continuous (fun p : P => (observedDiagonal p.1 i : ℂ)) :=
    Complex.continuous_ofReal.comp (hg i)
  simp only [adapted_iff_equations, adaptedEquations, Antitone, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_eq hU₁₁ continuous_const).inter ?_
  refine (isClosed_eq hV₂₂ continuous_const).inter ?_
  refine (isClosed_eq hU₂₁ hU₁₂.matrix_transpose.neg).inter ?_
  refine (isClosed_eq hV₂₁ hV₁₂.matrix_transpose.neg).inter ?_
  refine (isClosed_eq hB₂₁ ((continuous_pi hgC).matrix_diagonal)).inter ?_
  refine (isClosed_iInter fun i => isClosed_le continuous_const (hg i)).inter ?_
  refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (hg j) (hg i)).inter ?_
  refine (isClosed_eq (hg 2) continuous_const).inter ?_
  refine (isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (((hgC i).mul (hgC j)).mul (hU₂₂.matrix_elem i j)) continuous_const).inter ?_
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (((hgC i).mul (hgC j)).mul (hV₁₁.matrix_elem i j)) continuous_const

/-- With `B` fixed, existence of an adapted unitary basis is closed in the real pair `(U,V)`. -/
theorem isClosed_hasAdaptedBasis (B : Matrix OrderSixIndices OrderSixIndices ℝ) :
    IsClosed {p : Matrix OrderSixIndices OrderSixIndices ℝ × Matrix OrderSixIndices OrderSixIndices ℝ |
      HasAdaptedBasis B p.1 p.2} := by
  let EType := Matrix.unitaryGroup OrderSixIndices ℂ
  let : CompactSpace EType := isCompact_iff_compactSpace.mp isCompact_unitaryGroup
  let f (p : (RealMatrix × RealMatrix) × EType) : ComplexMatrix × ComplexMatrix × ComplexMatrix :=
    (unitarySimilarity p.2.val (complexify B), unitaryCongruence p.2.val (complexify p.1.1),
      unitaryCongruence p.2.val (complexify p.1.2))
  have hf : Continuous f := by
    unfold f unitarySimilarity unitaryCongruence
    fun_prop
  let S := {p : (RealMatrix × RealMatrix) × EType | Nonempty (AdaptedBlockForm (f p).1 (f p).2.1 (f p).2.2)}
  have hS : IsClosed S := isClosed_adaptedForm.preimage hf
  have hEq : {p : RealMatrix × RealMatrix | HasAdaptedBasis B p.1 p.2} = Prod.fst '' S := by
    ext p
    constructor
    · rintro ⟨E, hE, h⟩
      exact ⟨(p, ⟨E, hE⟩), h, rfl⟩
    · rintro ⟨⟨q, E⟩, h, rfl⟩
      exact ⟨E.val, E.property, h⟩
  rw [hEq]
  exact isClosedMap_fst_of_compactSpace S hS

set_option maxHeartbeats 500000 in
/-- The adapted-basis property extends to the closure of any set of admissible pairs. -/
theorem hasAdaptedBasis_of_mem_closure (B U V : Matrix OrderSixIndices OrderSixIndices ℝ)
    {s : Set (Matrix OrderSixIndices OrderSixIndices ℝ × Matrix OrderSixIndices OrderSixIndices ℝ)}
    (h : ∀ p ∈ s, HasAdaptedBasis B p.1 p.2) (hp : (U, V) ∈ closure s) : HasAdaptedBasis B U V := by
  have hsubset : s ⊆ {p : RealMatrix × RealMatrix | HasAdaptedBasis B p.1 p.2} := by
    intro p hp'
    exact h p hp'
  exact closure_minimal hsubset (isClosed_hasAdaptedBasis B) hp

end SymmetricMaximizer
