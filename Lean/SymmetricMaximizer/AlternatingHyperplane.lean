module

public import SymmetricMaximizer.Selection
public import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Tactic

/-!
# Restriction of an alternating form to a hyperplane

Wedging with a nonzero defining covector converts a two-form on a
hyperplane of a three-plane into a three-form. The latter can be
evaluated without choosing a moving frame of the hyperplane.
-/

@[expose] public section

open Module

namespace SymmetricMaximizer.Geometry

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Exterior product of a covector and an alternating bilinear form. -/
noncomputable def threeForm (l : W →ₗ[ℂ] ℂ) (a : LinearMap.BilinForm ℂ W) (ha : a.IsAlt) :
    AlternatingMap ℂ W ℂ (Fin 3) where
  toFun v := l (v 0) * a (v 1) (v 2) - l (v 1) * a (v 0) (v 2) +
    l (v 2) * a (v 0) (v 1)
  map_update_add' v i x y := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    all_goals
      simp only [Function.update_self, Function.update_of_ne (by omega : (0 : Fin 3) ≠ 1),
        Function.update_of_ne (by omega : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by omega : (0 : Fin 3) ≠ 2),
        Function.update_of_ne (by omega : (2 : Fin 3) ≠ 0),
        Function.update_of_ne (by omega : (1 : Fin 3) ≠ 2),
        Function.update_of_ne (by omega : (2 : Fin 3) ≠ 1),
        map_add, LinearMap.add_apply]
      ring
  map_update_smul' v i r x := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    all_goals
      simp only [Function.update_self, Function.update_of_ne (by omega : (0 : Fin 3) ≠ 1),
        Function.update_of_ne (by omega : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by omega : (0 : Fin 3) ≠ 2),
        Function.update_of_ne (by omega : (2 : Fin 3) ≠ 0),
        Function.update_of_ne (by omega : (1 : Fin 3) ≠ 2),
        Function.update_of_ne (by omega : (2 : Fin 3) ≠ 1),
        map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
      ring
  map_eq_zero_of_eq' v i j h hne := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    all_goals
      first
      | exact (hne rfl).elim
      | rw [h]
        simp only [ha.self_eq_zero, mul_zero, add_zero, sub_self, sub_zero]
        first
        | done
        | solve | ring
        | rw [← ha.neg_eq (v 0) (v 1)]; ring
        | rw [← ha.neg_eq (v 2) (v 1)]; ring

theorem threeForm_apply (l : W →ₗ[ℂ] ℂ) (a : LinearMap.BilinForm ℂ W) (ha : a.IsAlt)
    (v : Fin 3 → W) :
    threeForm l a ha v = l (v 0) * a (v 1) (v 2) - l (v 1) * a (v 0) (v 2) +
      l (v 2) * a (v 0) (v 1) :=
  rfl

/-- The three-form tests vanishing of the original form on the hyperplane of the covector. -/
theorem form_zero_on_hyperplane (l : W →ₗ[ℂ] ℂ) (a : LinearMap.BilinForm ℂ W) (ha : a.IsAlt)
    (u : Fin 3 → W) (h : threeForm l a ha u = 0)
    {x y z : W} (hx : x ∈ Submodule.span ℂ (Set.range u))
    (hy : y ∈ Submodule.span ℂ (Set.range u)) (hz : z ∈ Submodule.span ℂ (Set.range u))
    (hlx : l x ≠ 0) (hly : l y = 0) (hlz : l z = 0) : a y z = 0 := by
  let F := Fintype.linearCombination ℂ u
  have hF : (threeForm l a ha).compLinearMap F = 0 := by
    apply (Pi.basisFun ℂ (Fin 3)).ext_alternating
    intro v hv
    let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
    have hvals : (fun i => F ((Pi.basisFun ℂ (Fin 3)) (v i))) = u ∘ σ := by
      funext i
      simp [F, σ, Fintype.linearCombination_apply_single]
    change threeForm l a ha (fun i => F ((Pi.basisFun ℂ (Fin 3)) (v i))) = 0
    rw [hvals, (threeForm l a ha).map_perm, h, smul_zero]
  obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
  have hp' : F p = x := (Fintype.linearCombination_apply ℂ u p).trans hp
  have hq' : F q = y := (Fintype.linearCombination_apply ℂ u q).trans hq
  have hr' : F r = z := (Fintype.linearCombination_apply ℂ u r).trans hr
  have hval := DFunLike.congr_fun hF ![p, q, r]
  change threeForm l a ha (fun i => F (![p, q, r] i)) = 0 at hval
  simp only [threeForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, show ![p, q, r] 2 = r from rfl,
    hp', hq', hr', hly, hlz, zero_mul, sub_zero, add_zero] at hval
  exact (mul_eq_zero.mp hval).resolve_left hlx

/-- A quotient-line coordinate relative to a nonzero vector in a two-plane. -/
def quotientCoordinate (v w : Fin 2 → ℂ) : ℂ := v 0 * w 1 - v 1 * w 0

theorem quotientCoordinate_eq_zero {v w : Fin 2 → ℂ} (hv : v ≠ 0) :
    quotientCoordinate v w = 0 ↔ ∃ c : ℂ, c • v = w := by
  constructor
  · intro h
    unfold quotientCoordinate at h
    have he : v 0 * w 1 = v 1 * w 0 := sub_eq_zero.mp h
    by_cases hv₀ : v 0 = 0
    · have hv₁ : v 1 ≠ 0 := by
        intro h₁
        apply hv
        funext i
        fin_cases i <;> assumption
      have hw₀ : w 0 = 0 := by simpa [hv₀, hv₁, eq_comm] using he
      refine ⟨w 1 / v 1, funext fun i => ?_⟩
      fin_cases i
      · simp [hv₀, hw₀]
      · exact div_mul_cancel₀ _ hv₁
    · refine ⟨w 0 / v 0, funext fun i => ?_⟩
      fin_cases i
      · exact div_mul_cancel₀ _ hv₀
      · change w 0 / v 0 * v 1 = w 1
        field_simp
        linear_combination -he
  · rintro ⟨c, rfl⟩
    simp only [quotientCoordinate, Pi.smul_apply, smul_eq_mul]
    ring

end SymmetricMaximizer.Geometry
