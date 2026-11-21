module

public import SymmetricMaximizer.Basic
public import SymmetricMaximizer.ChernCalculation
public import SymmetricMaximizer.Elimination
public import SymmetricMaximizer.SelectionTheorem
public import SymmetricMaximizer.Maximizers
public import SymmetricMaximizer.SelectionReduction
public import SymmetricMaximizer.Sharpness

/-!
# Symmetric maximizers of Lyapunov operators

`SymmetricMaximizer.all_orders` gives the all-orders norm comparison.
`SymmetricMaximizer.symmetric_maximizers_all_orders` states the equivalent result
on attainment of the Lyapunov norm in every positive order.
`SymmetricMaximizer.exists_integer_counterexample` proves the integer counterexamples.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Frobenius

namespace SymmetricMaximizer

/-- The universal comparison of the two restricted Lyapunov norms holds exactly
in orders at most six. -/
theorem all_orders (n : ℕ) :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, skewNorm A ≤ symmetricNorm A) ↔ n ≤ 6 :=
  all_orders_of_sectionHasZero (selectionSectionHasZero (W := OrderSixHermitianSpace)) n

/-- In positive orders, every Lyapunov operator has a symmetric unit maximizer
exactly in orders at most six. -/
theorem symmetric_maximizers_all_orders (n : ℕ) (hn : 0 < n) :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, ∃ X : Matrix (Fin n) (Fin n) ℝ,
      Xᵀ = X ∧ ‖X‖ = 1 ∧ ‖lyapunov A X‖ = (lyapunovOperator A).opNorm) ↔ n ≤ 6 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (forall_congr' exists_symmetric_maximizer_iff).trans (all_orders n)

end SymmetricMaximizer
