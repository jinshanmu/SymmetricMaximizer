module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
# Singular bases for the compression in `lem:unitary`

The positive singular directions span the orthogonal complement of the kernel and
the corresponding left directions span the image. The singular values are ordered
by mathlib's definition.
-/

public section

open Module LinearMap Set
open scoped InnerProductSpace

namespace SymmetricMaximizer

/-- An orthonormal singular basis on each side of a map between equal finite dimensions. -/
theorem exists_singular_bases {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {n : ℕ} (g : E →ₗ[ℂ] F) (hE : finrank ℂ E = n) (hF : finrank ℂ F = n) :
    ∃ (v : OrthonormalBasis (Fin n) ℂ E) (w : OrthonormalBasis (Fin n) ℂ F) (s : Fin n → ℝ),
      (∀ i, 0 ≤ s i) ∧ Antitone s ∧
      (∀ i : Fin n, finrank ℂ (LinearMap.range g) ≤ (i : ℕ) → s i = 0) ∧
      (∀ i, g (v i) = (s i : ℂ) • w i) ∧
      ∀ i, s i ≠ 0 → v i ∈ (LinearMap.ker g)ᗮ ∧ w i ∈ LinearMap.range g := by
  classical
  let T := g.adjoint ∘ₗ g
  let v := g.isSymmetric_adjoint_comp_self.eigenvectorBasis hE
  let s (i : Fin n) := g.singularValues i
  have heig (i : Fin n) : g.adjoint (g (v i)) = (s i : ℂ) ^ 2 • v i := by
    change T (v i) = _
    rw [← Complex.ofReal_pow, show s i ^ 2 = g.isSymmetric_adjoint_comp_self.eigenvalues hE i from
      g.sq_singularValues_fin hE i]
    exact g.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hE i
  have hinner (i j : Fin n) : inner ℂ (g (v i)) (g (v j)) =
      (s j : ℂ) ^ 2 * (if i = j then 1 else 0) := by
    rw [← g.adjoint_inner_right, heig j, inner_smul_right, orthonormal_iff_ite.mp v.orthonormal]
  let target (i : Fin n) := (s i : ℂ)⁻¹ • g (v i)
  let active : Set (Fin n) := {i | s i ≠ 0}
  have horth : Orthonormal ℂ (active.domRestrict target) := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℂ (target i.val) (target j.val) = _
    by_cases hij : i = j
    · subst j
      have hi : (s i.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr i.property
      simp only [target, inner_smul_left, inner_smul_right, hinner, ite_true, mul_one]
      rw [show (starRingEnd ℂ) ((s i.val : ℂ)⁻¹) = (s i.val : ℂ)⁻¹ by simp]
      field_simp
    · have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [target, inner_smul_left, inner_smul_right, hinner, hne, hij]
  obtain ⟨w, hw⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (hF.trans (Fintype.card_fin n).symm) horth
  refine ⟨v, w, s, fun i => g.singularValues_nonneg i,
    fun _ _ hij => g.singularValues_antitone hij,
    fun i hi => (g.singularValues_eq_zero_iff_le_finrank_range (n := i)).mpr hi, ?_, ?_⟩
  · intro i
    by_cases hi : s i = 0
    · rw [hi, Complex.ofReal_zero, zero_smul]
      have h : inner ℂ (g (v i)) (g (v i)) = 0 := by rw [hinner, hi]; simp
      exact (inner_self_eq_zero (𝕜 := ℂ)).mp h
    · rw [hw i hi]
      change g (v i) = (s i : ℂ) • ((s i : ℂ)⁻¹ • g (v i))
      rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hi), one_smul]
  · intro i hi
    constructor
    · refine (Submodule.mem_orthogonal _ _).mpr fun x hx => ?_
      have h := g.adjoint_inner_right x (g (v i))
      rw [LinearMap.mem_ker.mp hx, inner_zero_left, heig i, inner_smul_right] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hi))
    · refine ⟨(s i : ℂ)⁻¹ • v i, ?_⟩
      rw [map_smul, hw i hi]

end SymmetricMaximizer
