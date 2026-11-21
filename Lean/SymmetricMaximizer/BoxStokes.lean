module

public import SymmetricMaximizer.Contraction
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# Integrating forms on a coordinate box

The top coefficient of an exterior derivative is a divergence.
On a collapsed face the flux vanishes as soon as it has a nonzero
tangent vector in the kernel of contraction.
-/

@[expose] public section

open Finset Module Set MeasureTheory
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

variable {n : ℕ}

/-- Coefficient of the oriented volume form. -/
noncomputable def topCoefficient (n : ℕ) : Exterior n →L[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Finset (Fin n) => ℝ) Finset.univ) ∘ₗ
    (exteriorBasis n).equivFun.toLinearMap).toContinuousLinearMap

theorem topCoefficient_basis (s : Finset (Fin n)) :
    topCoefficient n (exteriorBasis n s) = if s = Finset.univ then 1 else 0 := by
  change (exteriorBasis n).equivFun (exteriorBasis n s) Finset.univ = _
  rw [Basis.equivFun_self]

theorem topCoefficient_of_lower_degree {k : ℕ} (hk : k < n)
    {a : Exterior n} (ha : a ∈ ⋀[ℝ]^k (Coordinates n)) : topCoefficient n a = 0 := by
  let b := Pi.basisFun ℝ (Fin n)
  let V := ⋀[ℝ]^k (Coordinates n)
  have hzero : (topCoefficient n).toLinearMap ∘ₗ V.subtype = 0 := by
    apply (b.exteriorPower k).ext
    intro j
    change topCoefficient n ((b.exteriorPower k j : V) : Exterior n) = 0
    rw [← ExteriorAlgebra.basis_eq_coe_basis]
    change topCoefficient n (exteriorBasis n j.val) = 0
    rw [topCoefficient_basis]
    apply ite_eq_right
    intro he
    have hc := j.property
    change j.val.card = k at hc
    rw [he, Finset.card_univ, Fintype.card_fin] at hc
    omega
  exact DFunLike.congr_fun hzero (⟨a, ha⟩ : V)

private theorem contract_multi_mem (v : Coordinates n) (k : ℕ)
    (u : Fin (k + 1) → Coordinates n) :
    contract v (ExteriorAlgebra.ιMulti ℝ (k + 1) u) ∈ ⋀[ℝ]^k (Coordinates n) := by
  induction k with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, ← oneForm,
      contract_oneForm_mul, contract_one, mul_zero, sub_zero]
    apply Submodule.smul_mem
    let u₀ : Fin 0 → Coordinates n := fun i => nomatch i
    have hu₀ := ExteriorAlgebra.ιMulti_range ℝ 0 (Set.mem_range_self u₀)
    rwa [ExteriorAlgebra.ιMulti_zero_apply] at hu₀
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ← oneForm, contract_oneForm_mul]
    have htail : ExteriorAlgebra.ιMulti ℝ (k + 1) (Matrix.vecTail u) ∈
        ⋀[ℝ]^(k + 1) (Coordinates n) :=
      ExteriorAlgebra.ιMulti_range ℝ (k + 1) (Set.mem_range_self _)
    have hone : oneForm (u 0) ∈ ⋀[ℝ]^1 (Coordinates n) := by
      rw [show (⋀[ℝ]^1 (Coordinates n)) = LinearMap.range (oneForm (n := n)) from pow_one _]
      exact LinearMap.mem_range_self _ _
    have hprod := SetLike.mul_mem_graded (A := fun j => ⋀[ℝ]^j (Coordinates n))
      hone (ih (Matrix.vecTail u))
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ htail) (by simpa [Nat.add_comm] using hprod)

theorem topCoefficient_contract (v : Coordinates n) (a : Exterior n) :
    topCoefficient n (contract v a) = 0 := by
  have hmulti (k : ℕ) (hk : k ≤ n) (u : Fin k → Coordinates n) :
      topCoefficient n (contract v (ExteriorAlgebra.ιMulti ℝ k u)) = 0 := by
    cases k with
    | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
    | succ k => exact topCoefficient_of_lower_degree (by omega) (contract_multi_mem v k _)
  have hzero : (topCoefficient n).toLinearMap ∘ₗ (contract v).toLinearMap = 0 := by
    apply (exteriorBasis n).ext
    intro j
    change topCoefficient n (contract v (exteriorBasis n j)) = 0
    have hc : j.card ≤ n := by simpa using Finset.card_le_univ j
    simp only [exteriorBasis, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family]
    exact hmulti j.card hc _
  exact DFunLike.congr_fun hzero a

/-- The oriented coefficient on a coordinate face, with its outward sign at the upper face. -/
noncomputable def coordinateFlux (i : Fin n) : Exterior n →L[ℝ] ℝ :=
  (topCoefficient n).comp (exteriorMulL n (dx i))

@[simp] theorem coordinateFlux_apply (i : Fin n) (a : Exterior n) :
    coordinateFlux i a = topCoefficient n (dx i * a) := rfl

theorem coordinateFlux_eq_zero (i : Fin n) {v : Coordinates n} {a : Exterior n}
    (hv : v ≠ 0) (hvi : v i = 0) (ha : dx i * contract v a = 0) :
    coordinateFlux i a = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have h₁ : contract v (dx i * a) = 0 := by
    rw [dx, contract_oneForm_mul, evaluateOn_axis, hvi, zero_smul, zero_sub, neg_eq_zero]
    exact ha
  have h₂ := topCoefficient_contract v (dx j * (dx i * a))
  rw [show contract v (dx j * (dx i * a)) = v j • (dx i * a) by
    rw [dx, contract_oneForm_mul, evaluateOn_axis, h₁, mul_zero, sub_zero], map_smul] at h₂
  exact (smul_eq_zero.mp h₂).resolve_left hj

/-- Stokes' theorem for a smooth form in rectangular coordinates. -/
theorem integral_exteriorD_eq_flux {F : Coordinates (n + 1) → Exterior (n + 1)}
    (hF : ContDiff ℝ ∞ F) {a b : Coordinates (n + 1)} (hab : a ≤ b) :
    (∫ x in Icc a b, topCoefficient (n + 1) (exteriorD F x)) =
      ∑ i : Fin (n + 1),
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          coordinateFlux i (F (i.insertNth (b i) x))) -
          ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          coordinateFlux i (F (i.insertNth (a i) x))) := by
  let f (i : Fin (n + 1)) (x : Coordinates (n + 1)) := coordinateFlux i (F x)
  let f' (i : Fin (n + 1)) (x : Coordinates (n + 1)) :=
    (coordinateFlux i).comp (fderiv ℝ F x)
  have hd : ∀ i x, HasFDerivAt (f i) (f' i x) x := fun i x =>
    (coordinateFlux i).hasFDerivAt.comp x (hF.differentiable (by simp) x).hasFDerivAt
  have hdiv (x : Coordinates (n + 1)) :
      topCoefficient (n + 1) (exteriorD F x) = ∑ i, f' i x (Pi.single i 1) := by
    simp [exteriorD, directional, axis, f']
  have hi : IntegrableOn (fun x => ∑ i, f' i x (Pi.single i 1)) (Icc a b) := by
    simp_rw [← hdiv]
    have hc : Continuous (fun x => topCoefficient (n + 1) (exteriorD F x)) :=
      (topCoefficient (n + 1)).continuous.comp (smooth_exteriorD hF).continuous
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  simp_rw [hdiv]
  exact integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅ Set.countable_empty
    (fun i => ((coordinateFlux i).continuous.comp hF.continuous).continuousOn) (fun x _ i => hd i x) hi

end SymmetricMaximizer.Geometry
