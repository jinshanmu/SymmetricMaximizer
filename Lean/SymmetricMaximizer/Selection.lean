module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# The restrictions at a zero of the section in `lem:selection`

The fiberwise linear algebra of the selection lemma. A zero of the three components on
the flag `(L, ℓ)` gives all three restrictions on the compression `gₗ`.
-/

@[expose] public section

open Submodule

namespace SymmetricMaximizer

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- The map `L → Lᗮ` obtained by applying `B` and projecting orthogonally. -/
noncomputable def compression (B : W →ₗ[ℂ] W) (L : Submodule ℂ W) : L →ₗ[ℂ] Lᗮ :=
  Lᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ B ∘ₗ L.subtype

/-- The rank and alternating-form restrictions in the selection lemma follow at a section zero. -/
theorem selection_conclusions_of_section_zero (B : W →ₗ[ℂ] W) (α β : LinearMap.BilinForm ℂ W)
    (L : Submodule ℂ W) (ℓ : Submodule ℂ L) (hL : Module.finrank ℂ L = 3)
    (hℓ : Module.finrank ℂ ℓ = 1) :
    let g := compression B L
    ℓ ≤ LinearMap.ker g →
    (∀ x ∈ ℓᗮ, ∀ y ∈ ℓᗮ, α (x : W) (y : W) = 0) →
    (∀ x ∈ ℓᗮ, ∀ y ∈ ℓᗮ, β ((g x : Lᗮ) : W) ((g y : Lᗮ) : W) = 0) →
    Module.finrank ℂ (LinearMap.range g) ≤ 2 ∧
    (∀ x ∈ (LinearMap.ker g)ᗮ, ∀ y ∈ (LinearMap.ker g)ᗮ, α (x : W) (y : W) = 0) ∧
    (∀ u ∈ LinearMap.range g, ∀ v ∈ LinearMap.range g, β (u : W) (v : W) = 0) := by
  dsimp only
  let g := compression B L
  intro hker hα hβ
  have hrange : Module.finrank ℂ (LinearMap.range g) ≤ 2 := by
    have h := g.finrank_range_add_finrank_ker
    have h' : Module.finrank ℂ ℓ ≤ Module.finrank ℂ (LinearMap.ker g) :=
      Submodule.finrank_mono hker
    rw [hL] at h
    rw [hℓ] at h'
    omega
  have himage (u : Lᗮ) (hu : u ∈ LinearMap.range g) : ∃ x ∈ ℓᗮ, g x = u := by
    obtain ⟨z, rfl⟩ := hu
    have hz : z ∈ ℓ ⊔ ℓᗮ := by rw [ℓ.sup_orthogonal_of_hasOrthogonalProjection]; trivial
    obtain ⟨l, hl, x, hx, heq⟩ := Submodule.mem_sup.mp hz
    have hgl : g l = 0 := LinearMap.mem_ker.mp (hker hl)
    exact ⟨x, hx, by rw [← heq, map_add, hgl, zero_add]⟩
  refine ⟨hrange, fun x hx y hy => hα x (orthogonal_le hker hx) y (orthogonal_le hker hy), ?_⟩
  intro u hu v hv
  obtain ⟨x, hx, rfl⟩ := himage u hu
  obtain ⟨y, hy, rfl⟩ := himage v hv
  exact hβ x hx y hy

end SymmetricMaximizer
