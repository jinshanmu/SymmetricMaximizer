module

public import SymmetricMaximizer.ProjectiveBox
public import SymmetricMaximizer.ChernTransgression
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# The line connections of the selection bundle

The polar forms give the connections on the base tautological lines
and on the tautological line of the projectivization. The five
connection forms of the selection bundle represent the Chern roots
`t + hᵢ` and twice `h - t` from the manuscript.
-/

@[expose] public section

open Finset
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

/-- Squared modulus of the second entry of a polar pair. -/
noncomputable def polarArea (k : Fin 5) (x : Coordinates 10) : ℝ :=
  Real.sin (x (amplitudeIndex k)) ^ 2

/-- Derivative of the squared modulus with respect to the amplitude. -/
noncomputable def polarAreaDeriv (k : Fin 5) (x : Coordinates 10) : ℝ :=
  2 * Real.sin (x (amplitudeIndex k)) * Real.cos (x (amplitudeIndex k))

theorem smooth_polarArea (k : Fin 5) : ContDiff ℝ ∞ (polarArea k) := by
  unfold polarArea
  fun_prop

theorem scalarD_polarArea (k : Fin 5) (x : Coordinates 10) :
    scalarD (polarArea k) x = polarAreaDeriv k x • dx (amplitudeIndex k) := by
  let l : Coordinates 10 →L[ℝ] ℝ := ContinuousLinearMap.proj (amplitudeIndex k)
  have hd := ((Real.hasDerivAt_sin (l x)).pow 2).comp_hasFDerivAt x l.hasFDerivAt
  unfold scalarD dx
  rw [← map_smul]
  apply congrArg (fun v : Coordinates 10 => oneForm v)
  funext i
  have hf : fderiv ℝ (polarArea k) x = _ := hd.fderiv
  change (fderiv ℝ (polarArea k) x) (axis i) = _
  rw [hf, smul_apply, Pi.smul_apply]
  by_cases hi : i = amplitudeIndex k
  · subst i
    simp [l, polarAreaDeriv]
  · have hi' := Ne.symm hi
    simp [l, hi, hi', polarAreaDeriv]

/-- Reference connection for the indicated hyperplane class on the base. -/
noncomputable def baseConnection (k : Fin 3) (x : Coordinates 10) : Exterior 10 :=
  polarArea (basePair k) x • dx (phaseIndex (basePair k))

private theorem baseConnection_eval (k : Fin 3) (i : Fin 10) (side : Bool)
    (x : Coordinates 10) (hx : x i = projectiveBox.face i side) :
    contract (projectiveBox.tangent i side) (baseConnection k x) = baseCharge k i side • 1 := by
  rw [baseConnection, map_smul, contract_dx, smul_smul]
  congr 1
  fin_cases i <;> cases side <;> fin_cases k <;>
    norm_num [projectiveBox, BoxCycle.face, collapseDirection, baseCharge, basePair,
      amplitudeIndex, phaseIndex, polarArea, Pi.add_apply, Pi.sub_apply] at hx ⊢
  all_goals
    rw [hx]
    norm_num

theorem baseConnection_laws (k : Fin 3) :
    BoxConnection projectiveBox (baseCharge k) (baseConnection k) := by
  have hs : ContDiff ℝ ∞ (baseConnection k) := by
    unfold baseConnection
    have hc : ContDiff ℝ ∞ (fun _ : Coordinates 10 => dx (phaseIndex (basePair k))) :=
      contDiff_const
    exact (smooth_polarArea (basePair k)).smul hc
  refine ⟨hs, fun x => ?_,
    ?_, ?_, fun i _ side x hx => baseConnection_eval k i side x hx⟩
  · simp [baseConnection, dx, smul_neg]
  · intro i hi x
    simp only [baseConnection, polarArea, period_amplitude i hi]
  · intro i _ side x _ s
    simp [baseConnection, polarArea, Pi.add_apply, Pi.smul_apply, collapse_amplitude]

/-- Curvature of the indicated base connection. -/
noncomputable def baseCurvature (k : Fin 3) (x : Coordinates 10) : Exterior 10 :=
  polarAreaDeriv (basePair k) x •
    (dx (amplitudeIndex (basePair k)) * dx (phaseIndex (basePair k)))

theorem exteriorD_baseConnection (k : Fin 3) (x : Coordinates 10) :
    exteriorD (baseConnection k) x = baseCurvature k x := by
  unfold baseConnection baseCurvature
  rw [exteriorD_smul ((smooth_polarArea _).differentiable (by simp) x)
    (differentiableAt_const _), exteriorD_const, smul_zero, add_zero, scalarD_polarArea,
    smul_mul_assoc]

/-- Relative phase covector for the middle fiber coordinate. -/
noncomputable def fiberAngle₁ (x : Coordinates 10) : Exterior 10 :=
  baseConnection 1 x - baseConnection 0 x + dx 7

/-- Relative phase covector for the last fiber coordinate. -/
noncomputable def fiberAngle₂ (x : Coordinates 10) : Exterior 10 :=
  baseConnection 2 x - baseConnection 0 x + dx 9

/-- The angular interpolation on the last polar pair of the fiber. -/
noncomputable def fiberAngle (x : Coordinates 10) : Exterior 10 :=
  fiberAngle₁ x + polarArea 4 x • (fiberAngle₂ x - fiberAngle₁ x)

/-- Reference connection for the tautological class of the projectivization. -/
noncomputable def tautConnection (x : Coordinates 10) : Exterior 10 :=
  baseConnection 0 x + polarArea 3 x • fiberAngle x

private theorem smooth_fiberAngle₁ : ContDiff ℝ ∞ fiberAngle₁ :=
  ((baseConnection_laws 1).smooth.sub (baseConnection_laws 0).smooth).add contDiff_const

private theorem smooth_fiberAngle₂ : ContDiff ℝ ∞ fiberAngle₂ :=
  ((baseConnection_laws 2).smooth.sub (baseConnection_laws 0).smooth).add contDiff_const

private theorem smooth_fiberAngle : ContDiff ℝ ∞ fiberAngle :=
  smooth_fiberAngle₁.add ((smooth_polarArea 4).smul (smooth_fiberAngle₂.sub smooth_fiberAngle₁))

private theorem tautConnection_eval (i : Fin 10) (hi : i ∉ projectiveBox.periodic)
    (side : Bool) (x : Coordinates 10) (hx : x i = projectiveBox.face i side) :
    contract (projectiveBox.tangent i side) (tautConnection x) = tautCharge i side • 1 := by
  unfold tautConnection fiberAngle fiberAngle₁ fiberAngle₂
  simp only [map_add, map_sub, map_smul, contract_dx, baseConnection_eval _ i side x hx]
  change ¬ i.val % 2 = 1 at hi
  fin_cases i <;> cases side
  all_goals
    first
    | exact (hi (by decide)).elim
    | norm_num [projectiveBox, BoxCycle.face, collapseDirection, baseCharge, tautCharge,
        amplitudeIndex, basePair, polarArea, Pi.add_apply, Pi.sub_apply] at hx ⊢
  all_goals simp [hx]

theorem tautConnection_laws : BoxConnection projectiveBox tautCharge tautConnection := by
  refine ⟨(baseConnection_laws 0).smooth.add ((smooth_polarArea 3).smul smooth_fiberAngle),
    fun x => ?_, ?_, ?_, tautConnection_eval⟩
  · simp only [tautConnection, fiberAngle, fiberAngle₁, fiberAngle₂, map_add, map_sub, map_smul,
      (baseConnection_laws _).odd, dx, parity_oneForm]
    module
  · intro i hi x
    simp only [tautConnection, fiberAngle, fiberAngle₁, fiberAngle₂,
      (baseConnection_laws _).periodic i hi, polarArea, period_amplitude i hi]
  · intro i _ side x _ s
    simp [tautConnection, fiberAngle, fiberAngle₁, fiberAngle₂, baseConnection, polarArea,
      Pi.add_apply, Pi.smul_apply, collapse_amplitude]

/-- First decomposable fiber term in the tautological curvature. -/
noncomputable def tautFiber₁ (x : Coordinates 10) : Exterior 10 :=
  polarAreaDeriv 3 x • (dx 6 * fiberAngle x)

/-- Second decomposable fiber term in the tautological curvature. -/
noncomputable def tautFiber₂ (x : Coordinates 10) : Exterior 10 :=
  (polarArea 3 x * polarAreaDeriv 4 x) • (dx 8 * (fiberAngle₂ x - fiberAngle₁ x))

theorem exteriorD_tautConnection (x : Coordinates 10) :
    exteriorD tautConnection x =
      (1 - polarArea 3 x) • baseCurvature 0 x +
      (polarArea 3 x * (1 - polarArea 4 x)) • baseCurvature 1 x +
      (polarArea 3 x * polarArea 4 x) • baseCurvature 2 x +
      tautFiber₁ x + tautFiber₂ x := by
  have hn :  (∞ : ℕ∞ω) ≠ 0 := by simp
  have h₀ := (baseConnection_laws 0).smooth.differentiable hn x
  have h₁ := (baseConnection_laws 1).smooth.differentiable hn x
  have h₂ := (baseConnection_laws 2).smooth.differentiable hn x
  have h₃ := (smooth_polarArea 3).differentiable hn x
  have h₄ := (smooth_polarArea 4).differentiable hn x
  have hs₁ := smooth_fiberAngle₁.differentiable hn x
  have hs₂ := smooth_fiberAngle₂.differentiable hn x
  have hs := smooth_fiberAngle.differentiable hn x
  have h₁₀ : DifferentiableAt ℝ (fun y => baseConnection 1 y - baseConnection 0 y) x :=
    h₁.sub h₀
  have h₂₀ : DifferentiableAt ℝ (fun y => baseConnection 2 y - baseConnection 0 y) x :=
    h₂.sub h₀
  have h₂₁ : DifferentiableAt ℝ (fun y => fiberAngle₂ y - fiberAngle₁ y) x := hs₂.sub hs₁
  have hD₁ : exteriorD fiberAngle₁ x = baseCurvature 1 x - baseCurvature 0 x := by
    unfold fiberAngle₁
    rw [exteriorD_add h₁₀ (differentiableAt_const _), exteriorD_const,
      exteriorD_sub h₁ h₀, exteriorD_baseConnection, exteriorD_baseConnection, add_zero]
  have hD₂ : exteriorD fiberAngle₂ x = baseCurvature 2 x - baseCurvature 0 x := by
    unfold fiberAngle₂
    rw [exteriorD_add h₂₀ (differentiableAt_const _), exteriorD_const,
      exteriorD_sub h₂ h₀, exteriorD_baseConnection, exteriorD_baseConnection, add_zero]
  have hD : exteriorD fiberAngle x =
      exteriorD fiberAngle₁ x + (polarAreaDeriv 4 x) • (dx 8 * (fiberAngle₂ x - fiberAngle₁ x)) +
      polarArea 4 x • (exteriorD fiberAngle₂ x - exteriorD fiberAngle₁ x) := by
    unfold fiberAngle
    have hsc : DifferentiableAt ℝ
        (fun y => polarArea 4 y • (fiberAngle₂ y - fiberAngle₁ y)) x := h₄.smul h₂₁
    rw [exteriorD_add hs₁ hsc, exteriorD_smul h₄ h₂₁,
      exteriorD_sub hs₂ hs₁, scalarD_polarArea, smul_mul_assoc, add_assoc]
    rfl
  have hsc : DifferentiableAt ℝ (fun y => polarArea 3 y • fiberAngle y) x := h₃.smul hs
  unfold tautConnection
  rw [exteriorD_add h₀ hsc, exteriorD_smul h₃ hs, exteriorD_baseConnection,
    scalarD_polarArea, smul_mul_assoc, hD, hD₁, hD₂]
  unfold tautFiber₁ tautFiber₂
  change baseCurvature 0 x + (_ • (dx 6 * fiberAngle x) + _) = _
  module

/-- Connection for the determinant dual of the complement of the tautological line. -/
noncomputable def determinantConnection (x : Coordinates 10) : Exterior 10 :=
  (baseConnection 0 x + baseConnection 1 x + baseConnection 2 x) - tautConnection x

/-- Characters of the three quotient-line factors and the two determinant-line factors. -/
noncomputable def selectionCharge (j : Fin 5) (i : Fin 10) (side : Bool) : ℝ :=
  if h : j.val < 3 then tautCharge i side + baseCharge ⟨j.val, h⟩ i side
  else baseCharge 0 i side + baseCharge 1 i side + baseCharge 2 i side - tautCharge i side

/-- Connections on the five line factors of the bundle in the selection lemma. -/
noncomputable def selectionConnection (j : Fin 5) (x : Coordinates 10) : Exterior 10 :=
  if h : j.val < 3 then tautConnection x + baseConnection ⟨j.val, h⟩ x
  else determinantConnection x

/-- Adding line connections adds the boundary characters. -/
theorem BoxConnection.add {n : ℕ} {b : BoxCycle n} {c d : Fin n → Bool → ℝ}
    {A B : Coordinates n → Exterior n} (hA : BoxConnection b c A) (hB : BoxConnection b d B) :
    BoxConnection b (fun i side => c i side + d i side) (fun x => A x + B x) := by
  refine ⟨hA.smooth.add hB.smooth, fun x => by rw [map_add, hA.odd x, hB.odd x, neg_add],
    fun i hi x => by rw [hA.periodic i hi x, hB.periodic i hi x],
    fun i hi side x hx t => by rw [mul_add, mul_add, hA.invariant i hi side x hx t,
      hB.invariant i hi side x hx t],
    fun i hi side x hx => by rw [map_add, hA.evaluates i hi side x hx, hB.evaluates i hi side x hx,
      add_smul]⟩

/-- Subtracting line connections subtracts the boundary characters. -/
theorem BoxConnection.sub {n : ℕ} {b : BoxCycle n} {c d : Fin n → Bool → ℝ}
    {A B : Coordinates n → Exterior n} (hA : BoxConnection b c A) (hB : BoxConnection b d B) :
    BoxConnection b (fun i side => c i side - d i side) (fun x => A x - B x) := by
  refine ⟨hA.smooth.sub hB.smooth, fun x => by rw [map_sub, hA.odd x, hB.odd x]; abel,
    fun i hi x => by rw [hA.periodic i hi x, hB.periodic i hi x],
    fun i hi side x hx t => by rw [mul_sub, mul_sub, hA.invariant i hi side x hx t,
      hB.invariant i hi side x hx t],
    fun i hi side x hx => by rw [map_sub, hA.evaluates i hi side x hx, hB.evaluates i hi side x hx,
      sub_smul]⟩

theorem selectionConnection_laws (j : Fin 5) :
    BoxConnection projectiveBox (selectionCharge j) (selectionConnection j) := by
  by_cases hj : j.val < 3
  · have hA : selectionConnection j = fun x => tautConnection x + baseConnection ⟨j.val, hj⟩ x := by
      funext x
      simp [selectionConnection, hj]
    have hc : selectionCharge j = fun i side => tautCharge i side + baseCharge ⟨j.val, hj⟩ i side := by
      funext i side
      simp [selectionCharge, hj]
    rw [hA, hc]
    exact tautConnection_laws.add (baseConnection_laws ⟨j.val, hj⟩)
  · have hA : selectionConnection j = determinantConnection := by
      funext x
      simp [selectionConnection, hj]
    have hc : selectionCharge j =
        fun i side => baseCharge 0 i side + baseCharge 1 i side + baseCharge 2 i side - tautCharge i side := by
      funext i side
      simp [selectionCharge, hj]
    rw [hA, hc]
    exact (((baseConnection_laws 0).add (baseConnection_laws 1)).add
      (baseConnection_laws 2)).sub tautConnection_laws

end SymmetricMaximizer.Geometry
