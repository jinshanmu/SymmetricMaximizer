module

public import SymmetricMaximizer.Selection
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Orthogonal projection for a moving frame

The inverse Gram matrix gives the orthogonal projection onto the
span of a linearly independent family. This also proves smoothness
of the complementary projection when the frame is smooth.
-/

@[expose] public section

open Finset Matrix Submodule
open scoped BigOperators InnerProductSpace ContDiff

namespace SymmetricMaximizer.Geometry

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hermitian Gram matrix of a family. -/
noncomputable def frameGram (u : ι → W) : Matrix ι ι ℂ :=
  Matrix.of fun i j => inner ℂ (u i) (u j)

omit [DecidableEq ι] in
theorem frameGram_mulVec (u : ι → W) (a : ι → ℂ) (i : ι) :
    (frameGram u *ᵥ a) i = inner ℂ (u i) (∑ j, a j • u j) := by
  simp [frameGram, Matrix.mulVec, dotProduct, inner_sum, inner_smul_right, mul_comm]

theorem frameGram_det_ne_zero {u : ι → W} (hu : LinearIndependent ℂ u) :
    (frameGram u).det ≠ 0 := by
  intro hd
  obtain ⟨a, ha, hGa⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := frameGram u)).mpr hd
  let y := ∑ j, a j • u j
  have hinner (i : ι) : inner ℂ (u i) y = 0 := by
    rw [← frameGram_mulVec, hGa]
    rfl
  have hy : y = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    change inner ℂ (∑ j, a j • u j) y = 0
    simp [sum_inner, inner_smul_left, hinner]
  apply ha
  funext i
  exact Fintype.linearIndependent_iff.mp hu a hy i

/-- Orthogonal residual of a vector after solving the normal equations. -/
noncomputable def frameResidual (u : ι → W) (y : W) : W :=
  let b := fun i => inner ℂ (u i) y
  let a := (frameGram u)⁻¹ *ᵥ b
  y - ∑ i, a i • u i

theorem frameResidual_eq_projection [FiniteDimensional ℂ W]
    {u : ι → W} (hu : LinearIndependent ℂ u) (y : W) :
    frameResidual u y = (Submodule.span ℂ (Set.range u))ᗮ.starProjection y := by
  let L := Submodule.span ℂ (Set.range u)
  let b (i : ι) := inner ℂ (u i) y
  let a := (frameGram u)⁻¹ *ᵥ b
  let p := ∑ i, a i • u i
  have hp : p ∈ L :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨a, rfl⟩
  have hGa : frameGram u *ᵥ a = b := by
    dsimp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (frameGram_det_ne_zero hu)), Matrix.one_mulVec]
  have hi (i : ι) : inner ℂ (u i) (y - p) = 0 := by
    change inner ℂ (u i) (y - ∑ j, a j • u j) = 0
    rw [inner_sub_right, ← frameGram_mulVec, hGa]
    exact sub_self _
  have hperp : y - p ∈ Lᗮ := (L.mem_orthogonal _).mpr fun z hz => by
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
    simp [sum_inner, inner_smul_left, hi]
  change y - p = Lᗮ.starProjection y
  rw [Submodule.starProjection_orthogonal_val, L.eq_starProjection_of_mem_orthogonal hp hperp]

private theorem det_smooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : X → Matrix ι ι ℂ} (hG : ∀ i j, ContDiff ℝ ∞ (fun t => G t i j)) :
    ContDiff ℝ ∞ (fun t => (G t).det) := by
  simp only [Matrix.det_apply]
  exact ContDiff.sum fun σ _ => (contDiff_prod fun i _ => hG (σ i) i).const_smul σ.sign

private theorem inv_entries_smooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : X → Matrix ι ι ℂ} (hG : ∀ i j, ContDiff ℝ ∞ (fun t => G t i j))
    (hdet : ∀ t, (G t).det ≠ 0) (i j : ι) :
    ContDiff ℝ ∞ (fun t => (G t)⁻¹ i j) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((det_smooth hG).inv hdet).mul (det_smooth ?_)
  intro k l
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.updateRow_self] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : X => (Pi.single i 1 : ι → ℂ) l))
  · simpa only [Matrix.updateRow_ne hk] using hG k l

theorem smooth_frameResidual {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ι → W} {y : X → W}
    (hu : ∀ i, ContDiff ℝ ∞ (fun t => u t i)) (huind : ∀ t, LinearIndependent ℂ (u t))
    (hy : ContDiff ℝ ∞ y) : ContDiff ℝ ∞ (fun t => frameResidual (u t) (y t)) := by
  have hg (i j : ι) : ContDiff ℝ ∞ (fun t => frameGram (u t) i j) :=
    (hu i).inner ℂ (hu j)
  have hdet (t : X) : (frameGram (u t)).det ≠ 0 := frameGram_det_ne_zero (huind t)
  have hgInv := inv_entries_smooth hg hdet
  have hb (i : ι) : ContDiff ℝ ∞ (fun t => inner ℂ (u t i) (y t)) := (hu i).inner ℂ hy
  unfold frameResidual
  apply hy.sub
  apply ContDiff.sum
  intro i _
  apply ContDiff.smul _ (hu i)
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => (hgInv i j).mul (hb j)

end SymmetricMaximizer.Geometry
