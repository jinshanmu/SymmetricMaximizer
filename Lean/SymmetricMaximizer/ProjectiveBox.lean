module

public import SymmetricMaximizer.Phase
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Projective coordinates for the flag space

The five polar coordinate pairs describe three projective lines and a
projective plane in their sum. Opposite phase faces are periodic.
At either end of an amplitude interval a specified phase orbit
represents the same flag.
-/

@[expose] public section

open Finset
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

/-- The amplitude coordinate of a polar pair. -/
def amplitudeIndex (i : Fin 5) : Fin 10 := ⟨2 * i.val, by omega⟩

/-- The phase coordinate of a polar pair. -/
def phaseIndex (i : Fin 5) : Fin 10 := ⟨2 * i.val + 1, by omega⟩

/-- The three base coordinate pairs. -/
def basePair (i : Fin 3) : Fin 5 := Fin.castLE (by decide : 3 ≤ 5) i

/-- The phase orbit that collapses at the specified amplitude endpoint. -/
noncomputable def collapseDirection (i : Fin 10) (side : Bool) : Coordinates 10 :=
  if side then
    ![axis 1 + axis 7 + axis 9, 0, axis 3 - axis 7, 0, axis 5 - axis 9, 0,
      axis 7 + axis 9, 0, axis 7, 0] i
  else
    ![axis 1, 0, axis 3, 0, axis 5, 0, axis 7, 0, axis 9, 0] i

/-- The oriented polar box for the projectivization over the product of three lines. -/
noncomputable def projectiveBox : BoxCycle 10 where
  lower := 0
  upper := fun i => if i.val % 2 = 0 then Real.pi / 2 else 2 * Real.pi
  ordered := by
    intro i
    change (0 : ℝ) ≤ if i.val % 2 = 0 then Real.pi / 2 else 2 * Real.pi
    split <;> positivity
  periodic := {i | i.val % 2 = 1}
  tangent := collapseDirection
  tangent_ne_zero := by
    intro i hi side h
    change ¬ i.val % 2 = 1 at hi
    let k : Fin 10 := ![1, 1, 3, 3, 5, 5, 7, 7, if side then 7 else 9, 9] i
    have hk := congrFun h k
    fin_cases i <;> cases side <;> norm_num at hi <;>
      norm_num [k, collapseDirection, Pi.add_apply, Pi.sub_apply] at hk
  tangent_normal_zero := by
    intro i _ side
    fin_cases i <;> cases side <;>
      norm_num [collapseDirection, Pi.add_apply, Pi.sub_apply]

/-- The weight of the base tautological line along a collapsing orbit. -/
noncomputable def baseCharge (k : Fin 3) (i : Fin 10) (side : Bool) : ℝ :=
  if side = true ∧ i = amplitudeIndex (basePair k) then 1 else 0

/-- The weight of the tautological line in the three-plane along a collapsing orbit. -/
noncomputable def tautCharge (i : Fin 10) (side : Bool) : ℝ :=
  if side = true ∧ (i = 0 ∨ i = 6) then 1 else 0

/-- A unit representative of the indicated base line, in a fixed orthonormal frame. -/
noncomputable def baseRepresentative (k : Fin 3) (x : Coordinates 10) : Fin 2 → ℂ :=
  ![(Real.cos (x (amplitudeIndex (basePair k))) : ℂ),
    (Real.sin (x (amplitudeIndex (basePair k))) : ℂ) * phase (x (phaseIndex (basePair k)))]

/-- Unit coefficients for a line in the sum of the three base lines. -/
noncomputable def tautCoefficients (x : Coordinates 10) : Fin 3 → ℂ :=
  ![(Real.cos (x 6) : ℂ),
    (Real.sin (x 6) * Real.cos (x 8) : ℝ) * phase (x 7),
    (Real.sin (x 6) * Real.sin (x 8) : ℝ) * phase (x 9)]

theorem baseRepresentative_normSq (k : Fin 3) (x : Coordinates 10) :
    ∑ j : Fin 2, Complex.normSq (baseRepresentative k x j) = 1 := by
  simp [Fin.sum_univ_two, baseRepresentative, Complex.normSq_eq_norm_sq, norm_phase,
    -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem tautCoefficients_normSq (x : Coordinates 10) :
    ∑ k : Fin 3, Complex.normSq (tautCoefficients x k) = 1 := by
  simp [Fin.sum_univ_three, tautCoefficients, Complex.normSq_eq_norm_sq, norm_phase,
    -Complex.ofReal_cos, -Complex.ofReal_sin, sq_abs]
  calc
    _ = Real.cos (x 6) ^ 2 + Real.sin (x 6) ^ 2 *
      (Real.sin (x 8) ^ 2 + Real.cos (x 8) ^ 2) := by
      simp only [mul_pow, sq_abs]
      ring
    _ = 1 := by rw [Real.sin_sq_add_cos_sq, mul_one, add_comm, Real.sin_sq_add_cos_sq]

theorem period_amplitude (i : Fin 10) (hi : i ∈ projectiveBox.periodic)
    (x : Coordinates 10) (k : Fin 5) :
    (x + projectiveBox.period i) (amplitudeIndex k) = x (amplitudeIndex k) := by
  have hne : i ≠ amplitudeIndex k := by
    intro h
    subst i
    change (2 * k.val) % 2 = 1 at hi
    omega
  simp [BoxCycle.period, Pi.add_apply, Pi.smul_apply, hne]

private theorem period_phase (i : Fin 10) (hi : i ∈ projectiveBox.periodic)
    (x : Coordinates 10) (k : Fin 5) :
    phase ((x + projectiveBox.period i) (phaseIndex k)) = phase (x (phaseIndex k)) := by
  change i.val % 2 = 1 at hi
  by_cases h : i = phaseIndex k
  · rw [← h]
    have hp : projectiveBox.period i i = 2 * Real.pi := by
      simp [BoxCycle.period, projectiveBox, Pi.smul_apply, hi]
    rw [Pi.add_apply, hp, phase_periodic]
  · simp [BoxCycle.period, Pi.add_apply, Pi.smul_apply, h]

theorem baseRepresentative_periodic (i : Fin 10) (hi : i ∈ projectiveBox.periodic)
    (k : Fin 3) (x : Coordinates 10) :
    baseRepresentative k (x + projectiveBox.period i) = baseRepresentative k x := by
  simp only [baseRepresentative, period_amplitude i hi, period_phase i hi]

theorem tautCoefficients_periodic (i : Fin 10) (hi : i ∈ projectiveBox.periodic)
    (x : Coordinates 10) :
    tautCoefficients (x + projectiveBox.period i) = tautCoefficients x := by
  have h₆ := period_amplitude i hi x 3
  have h₈ := period_amplitude i hi x 4
  have h₇ := period_phase i hi x 3
  have h₉ := period_phase i hi x 4
  change (x + projectiveBox.period i) 6 = x 6 at h₆
  change (x + projectiveBox.period i) 8 = x 8 at h₈
  change phase ((x + projectiveBox.period i) 7) = phase (x 7) at h₇
  change phase ((x + projectiveBox.period i) 9) = phase (x 9) at h₉
  simp only [tautCoefficients, h₆, h₈, h₇, h₉]

theorem collapse_amplitude (i : Fin 10) (side : Bool) (k : Fin 5) :
    projectiveBox.tangent i side (amplitudeIndex k) = 0 := by
  fin_cases i <;> cases side <;> fin_cases k <;>
    norm_num [projectiveBox, collapseDirection, amplitudeIndex, Pi.add_apply, Pi.sub_apply]

theorem baseRepresentative_equivariant (i : Fin 10) (hi : i ∉ projectiveBox.periodic)
    (side : Bool) (k : Fin 3) (x : Coordinates 10) (hx : x i = projectiveBox.face i side)
    (s : ℝ) :
    baseRepresentative k (x + s • projectiveBox.tangent i side) =
      phase (s * baseCharge k i side) • baseRepresentative k x := by
  funext j
  change ¬ i.val % 2 = 1 at hi
  have ha := collapse_amplitude i side (basePair k)
  simp only [baseRepresentative, Pi.add_apply, Pi.smul_apply, ha, smul_eq_mul]
  fin_cases i <;> cases side <;> fin_cases k <;> fin_cases j
  all_goals
    first
    | exact (hi (by decide)).elim
    | simp [BoxCycle.face, projectiveBox] at hx
      norm_num [projectiveBox, collapseDirection, baseCharge, amplitudeIndex, phaseIndex, basePair,
        Pi.add_apply, Pi.sub_apply, hx, phase_add, mul_comm, mul_left_comm, mul_assoc]

theorem tautCoefficients_equivariant (i : Fin 10) (hi : i ∉ projectiveBox.periodic)
    (side : Bool) (k : Fin 3) (x : Coordinates 10) (hx : x i = projectiveBox.face i side)
    (s : ℝ) :
    tautCoefficients (x + s • projectiveBox.tangent i side) k =
      phase (s * (tautCharge i side - baseCharge k i side)) * tautCoefficients x k := by
  change ¬ i.val % 2 = 1 at hi
  have h₆ := collapse_amplitude i side 3
  have h₈ := collapse_amplitude i side 4
  change projectiveBox.tangent i side 6 = 0 at h₆
  change projectiveBox.tangent i side 8 = 0 at h₈
  simp only [tautCoefficients, Pi.add_apply, Pi.smul_apply, h₆, h₈, smul_zero, add_zero]
  fin_cases i <;> cases side <;> fin_cases k
  all_goals
    first
    | exact (hi (by decide)).elim
    | simp [BoxCycle.face, projectiveBox] at hx
      norm_num [projectiveBox, collapseDirection, tautCharge, baseCharge, amplitudeIndex, basePair,
        Pi.add_apply, Pi.sub_apply, hx, phase_add, mul_comm, mul_left_comm, mul_assoc]

end SymmetricMaximizer.Geometry
