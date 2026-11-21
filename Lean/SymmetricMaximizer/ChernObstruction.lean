module

public import SymmetricMaximizer.ChernTransgression
public import SymmetricMaximizer.Phase
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

/-!
# A nonzero Chern number forces a zero

A nowhere zero section of the sum of line bundles lets us change
each line connection to the angular differential where that component
is large. A smooth cutoff makes these choices global. Near every point
at least one curvature then vanishes. Transgression gives the required
top Chern vanishing for the original connections.
-/

@[expose] public section

open Finset Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace SymmetricMaximizer.Geometry

variable {n m : ℕ}

/-- Components of a section in polar frames, with the associated phase laws. -/
structure PhaseSection {m : ℕ} (b : BoxCycle n) (charge : Fin m → Fin n → Bool → ℝ)
    (f : Fin m → Coordinates n → ℂ) : Prop where
  smooth : ∀ j, ContDiff ℝ ∞ (f j)
  periodic : ∀ i ∈ b.periodic, ∀ j x, f j (x + b.period i) = f j x
  equivariant : ∀ i ∉ b.periodic, ∀ side j x, x i = b.face i side → ∀ s : ℝ,
    f j (x + s • b.tangent i side) = phase (s * charge j i side) * f j x

private noncomputable def totalNormSq (f : Fin m → Coordinates n → ℂ) (x : Coordinates n) : ℝ :=
  ∑ j, Complex.normSq (f j x)

private noncomputable def share (f : Fin m → Coordinates n → ℂ) (j : Fin m)
    (x : Coordinates n) : ℝ := Complex.normSq (f j x) / totalNormSq f x

private theorem totalNormSq_pos {f : Fin m → Coordinates n → ℂ}
    (h : ∀ x, ∃ j, f j x ≠ 0) (x : Coordinates n) : 0 < totalNormSq f x := by
  obtain ⟨j, hj⟩ := h x
  refine Finset.sum_pos' (fun k _ => Complex.normSq_nonneg (f k x)) ⟨j, mem_univ _, ?_⟩
  exact lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (mt Complex.normSq_eq_zero.mp hj))

private theorem smooth_share {f : Fin m → Coordinates n → ℂ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (h : ∀ x, ∃ j, f j x ≠ 0) (j : Fin m) :
    ContDiff ℝ ∞ (share f j) :=
  (smooth_normSq_comp (hf j)).div
    (ContDiff.sum fun k _ => smooth_normSq_comp (hf k))
    (fun x => (totalNormSq_pos h x).ne')

private noncomputable def cutoff (m : ℕ) (s : ℝ) : ℝ := Real.smoothTransition (4 * m * s - 1)

private noncomputable def cutoffDenom (m : ℕ) (z : ℂ) (s : ℝ) : ℝ :=
  Complex.normSq z + Real.smoothTransition (1 - 4 * m * s)

private theorem denom_pos {f : Fin m → Coordinates n → ℂ} (j : Fin m) (x : Coordinates n) :
    0 < cutoffDenom m (f j x) (share f j x) := by
  by_cases h : f j x = 0
  · norm_num [share, cutoffDenom, h, Real.smoothTransition.one]
  · exact add_pos_of_pos_of_nonneg
      (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (mt Complex.normSq_eq_zero.mp h)))
      (Real.smoothTransition.nonneg _)

private theorem denom_eq_of_cutoff_ne_zero {s : ℝ} (h : cutoff m s ≠ 0) (z : ℂ) :
    cutoffDenom m z s = Complex.normSq z := by
  have hs : 0 < 4 * (m : ℝ) * s - 1 := by
    by_contra! hle
    exact h (Real.smoothTransition.zero_of_nonpos hle)
  unfold cutoffDenom
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), add_zero]

private theorem cutoff_scale {f : Fin m → Coordinates n → ℂ} (j : Fin m) (x : Coordinates n) :
    (cutoff m (share f j x) / cutoffDenom m (f j x) (share f j x)) * Complex.normSq (f j x) =
      cutoff m (share f j x) := by
  by_cases h : cutoff m (share f j x) = 0
  · rw [h, zero_div, zero_mul]
  · have hd := (denom_pos (f := f) j x).ne'
    rw [← denom_eq_of_cutoff_ne_zero h (f j x)]
    exact div_mul_cancel₀ _ hd

private noncomputable def adjustedConnection (A : Fin m → Coordinates n → Exterior n)
    (f : Fin m → Coordinates n → ℂ) (j : Fin m) (x : Coordinates n) : Exterior n :=
  (1 - cutoff m (share f j x)) • A j x +
    (cutoff m (share f j x) / cutoffDenom m (f j x) (share f j x)) • angularNumerator (f j) x

private theorem share_congr {f : Fin m → Coordinates n → ℂ} {x y : Coordinates n}
    (h : ∀ j, Complex.normSq (f j x) = Complex.normSq (f j y)) (j : Fin m) :
    share f j x = share f j y := by
  simp only [share, totalNormSq, h]

private theorem cutoffDenom_congr {f : Fin m → Coordinates n → ℂ} {x y : Coordinates n}
    (h : ∀ j, Complex.normSq (f j x) = Complex.normSq (f j y)) (j : Fin m) :
    cutoffDenom m (f j x) (share f j x) = cutoffDenom m (f j y) (share f j y) := by
  rw [cutoffDenom, cutoffDenom, h j, share_congr h]

private theorem adjustedConnection_laws {b : BoxCycle n} {charge : Fin m → Fin n → Bool → ℝ}
    {A : Fin m → Coordinates n → Exterior n} {f : Fin m → Coordinates n → ℂ}
    (hA : ∀ j, BoxConnection b (charge j) (A j)) (hf : PhaseSection b charge f)
    (h : ∀ x, ∃ j, f j x ≠ 0) (j : Fin m) :
    BoxConnection b (charge j) (adjustedConnection A f j) := by
  have hs := smooth_share hf.smooth h j
  have hχ : ContDiff ℝ ∞ (fun x => cutoff m (share f j x)) := by
    unfold cutoff
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul hs).sub contDiff_const)
  have hd : ContDiff ℝ ∞ (fun x => cutoffDenom m (f j x) (share f j x)) :=
    (smooth_normSq_comp (hf.smooth j)).add
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul hs)))
  have hdj := (hf.smooth j).differentiable (by simp)
  refine ⟨((contDiff_const.sub hχ).smul (hA j).smooth).add
    ((hχ.div hd (fun x => (denom_pos j x).ne')).smul (smooth_angularNumerator (hf.smooth j))),
    fun x => ?_, ?_, ?_, ?_⟩
  · simp [adjustedConnection, (hA j).odd x, parity_angularNumerator, map_smul, smul_neg]
    abel
  · intro i hi x
    have hper : ∀ k, Complex.normSq (f k (x + b.period i)) = Complex.normSq (f k x) :=
      fun k => congrArg Complex.normSq (hf.periodic i hi k x)
    rw [adjustedConnection, adjustedConnection, cutoffDenom_congr hper j, share_congr hper j,
      (hA j).periodic i hi x, angularNumerator_periodic hdj (hf.periodic i hi j) x]
  · intro i hi side x hx s
    have hrot : ∀ k, Complex.normSq (f k (x + s • b.tangent i side)) = Complex.normSq (f k x) := by
      intro k
      rw [hf.equivariant i hi side k x hx s]
      simp [Complex.normSq_eq_norm_sq, norm_phase]
    rw [adjustedConnection, adjustedConnection, cutoffDenom_congr hrot j, share_congr hrot j]
    simp only [mul_add, mul_smul_comm]
    rw [(hA j).invariant i hi side x hx s,
      angularNumerator_face_invariant hdj hx (hf.equivariant i hi side j) s]
  · intro i hi side x hx
    rw [adjustedConnection, map_add, map_smul, map_smul, (hA j).evaluates i hi side x hx,
      contract_angularNumerator_orbit (hdj x) (charge j i side) (hf.equivariant i hi side j x hx)]
    simp only [smul_smul, ← add_smul]
    congr 1
    rw [← mul_assoc, cutoff_scale]
    ring

private theorem some_share_large {f : Fin m → Coordinates n → ℂ}
    (h : ∀ x, ∃ j, f j x ≠ 0) (x : Coordinates n) : ∃ j, 1 / 2 < (m : ℝ) * share f j x := by
  have hsum : ∑ j, share f j x = 1 := by
    simp only [share, ← Finset.sum_div]
    exact div_self (totalNormSq_pos h x).ne'
  have hm : (0 : ℝ) < m := by
    obtain ⟨j, _⟩ := h x
    exact_mod_cast Nat.zero_lt_of_lt j.isLt
  by_contra! hsmall
  have hb : ∑ j, (m : ℝ) * share f j x ≤ ∑ _j : Fin m, (1 / 2 : ℝ) :=
    Finset.sum_le_sum (fun j _ => hsmall j)
  rw [← Finset.mul_sum, hsum, mul_one] at hb
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  linarith

private theorem adjustedConnection_curvature_zero {A : Fin m → Coordinates n → Exterior n}
    {f : Fin m → Coordinates n → ℂ} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (h : ∀ x, ∃ j, f j x ≠ 0) {j : Fin m} {x : Coordinates n}
    (hj : 1 / 2 < (m : ℝ) * share f j x) : exteriorD (adjustedConnection A f j) x = 0 := by
  have hn : f j x ≠ 0 := by
    intro he
    norm_num [share, he] at hj
  have hevent : ∀ᶠ y in 𝓝 x, 1 / 2 < (m : ℝ) * share f j y :=
    (continuousAt_const.eventually_lt
      (continuous_const.mul (smooth_share hf h j).continuous).continuousAt hj)
  have he : adjustedConnection A f j =ᶠ[𝓝 x]
      (fun y => (Complex.normSq (f j y))⁻¹ • angularNumerator (f j) y) := by
    filter_upwards [hevent] with y hy
    have hχ : cutoff m (share f j y) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    have hd := denom_eq_of_cutoff_ne_zero (hχ ▸ one_ne_zero) (f j y)
    rw [adjustedConnection, hd, hχ, sub_self, zero_smul, zero_add, one_div]
  unfold exteriorD directional
  rw [he.fderiv_eq]
  exact exteriorD_angular (hf j) hn

/-- A nowhere-zero section makes the product of the line curvatures exact. -/
theorem exact_curvatureProduct_of_nonvanishing_section {b : BoxCycle n}
    {charge : Fin m → Fin n → Bool → ℝ} {A : Fin m → Coordinates n → Exterior n}
    {f : Fin m → Coordinates n → ℂ}
    (hA : ∀ j, BoxConnection b (charge j) (A j)) (hf : PhaseSection b charge f)
    (h : ∀ x, ∃ j, f j x ≠ 0) :
    ∃ K : Coordinates n → Exterior n, ContDiff ℝ ∞ K ∧ BoundaryBasic b K ∧
      exteriorD K = formProduct (fun j => exteriorD (A j)) := by
  obtain ⟨K, hs, hb, hK⟩ := exists_transgression hA (adjustedConnection_laws hA hf h)
  refine ⟨K, hs, hb, funext fun x => ?_⟩
  obtain ⟨j, hj⟩ := some_share_large h x
  have hz := formProduct_eq_zero_of_component (fun k => exteriorD (adjustedConnection A f k))
    (adjustedConnection_curvature_zero hf.smooth h hj)
  rw [hK, hz, sub_zero]

/-- A common zero exists if the top Chern integral is nonzero. -/
theorem exists_section_zero_of_chernIntegral_ne_zero {b : BoxCycle (n + 1)}
    {charge : Fin m → Fin (n + 1) → Bool → ℝ}
    {A : Fin m → Coordinates (n + 1) → Exterior (n + 1)}
    {f : Fin m → Coordinates (n + 1) → ℂ}
    (hA : ∀ j, BoxConnection b (charge j) (A j)) (hf : PhaseSection b charge f)
    (hint : integrateTop b (formProduct (fun j => exteriorD (A j))) ≠ 0) :
    ∃ x, ∀ j, f j x = 0 := by
  by_contra! h
  obtain ⟨K, hs, hb, hK⟩ := exact_curvatureProduct_of_nonvanishing_section hA hf h
  exact hint (hK ▸ integrateTop_exteriorD_zero hs hb)

end SymmetricMaximizer.Geometry
