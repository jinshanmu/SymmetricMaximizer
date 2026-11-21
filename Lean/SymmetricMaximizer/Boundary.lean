module

public import SymmetricMaximizer.BoxStokes
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Periodic and collapsing faces

A projective coordinate box has periodic phase faces and faces on which
a phase direction collapses. These are the two ways its Stokes boundary
terms cancel.
-/

@[expose] public section

open Finset Set MeasureTheory
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

variable {n : ℕ}

/-- Oriented box data with paired faces or a tangent direction of collapse. -/
structure BoxCycle (n : ℕ) where
  /-- Lower endpoint of each coordinate interval. -/
  lower : Coordinates n
  /-- Upper endpoint of each coordinate interval. -/
  upper : Coordinates n
  ordered : lower ≤ upper
  /-- Coordinates whose opposite faces are identified by translation. -/
  periodic : Set (Fin n)
  /-- A collapsed direction on each face that is not paired by translation. -/
  tangent : Fin n → Bool → Coordinates n
  tangent_ne_zero : ∀ i ∉ periodic, ∀ side, tangent i side ≠ 0
  tangent_normal_zero : ∀ i ∉ periodic, ∀ side, tangent i side i = 0

/-- The specified lower or upper endpoint of a coordinate. -/
noncomputable def BoxCycle.face (b : BoxCycle n) (i : Fin n) (side : Bool) : ℝ :=
  if side then b.upper i else b.lower i

/-- Translation identifying the opposite faces in a periodic coordinate. -/
noncomputable def BoxCycle.period (b : BoxCycle n) (i : Fin n) : Coordinates n :=
  (b.upper i - b.lower i) • axis i

/-- The form has matching values at periodic faces and is horizontal at collapsed faces. -/
structure BoundaryBasic (b : BoxCycle n) (F : Coordinates n → Exterior n) : Prop where
  periodic : ∀ i ∈ b.periodic, ∀ x, F (x + b.period i) = F x
  horizontal : ∀ i ∉ b.periodic, ∀ side x, x i = b.face i side →
    dx i * contract (b.tangent i side) (F x) = 0

theorem BoundaryBasic.add {b : BoxCycle n} {F G : Coordinates n → Exterior n}
    (hF : BoundaryBasic b F) (hG : BoundaryBasic b G) :
    BoundaryBasic b (fun x => F x + G x) := by
  refine ⟨fun i hi x => by rw [hF.periodic i hi x, hG.periodic i hi x], ?_⟩
  intro i hi side x hx
  rw [map_add, mul_add, hF.horizontal i hi side x hx, hG.horizontal i hi side x hx, add_zero]

theorem BoundaryBasic.sub {b : BoxCycle n} {F G : Coordinates n → Exterior n}
    (hF : BoundaryBasic b F) (hG : BoundaryBasic b G) :
    BoundaryBasic b (fun x => F x - G x) := by
  refine ⟨fun i hi x => by rw [hF.periodic i hi x, hG.periodic i hi x], ?_⟩
  intro i hi side x hx
  rw [map_sub, mul_sub, hF.horizontal i hi side x hx, hG.horizontal i hi side x hx, sub_zero]

theorem BoundaryBasic.mul {b : BoxCycle n} {F G : Coordinates n → Exterior n}
    (hF : BoundaryBasic b F) (hG : BoundaryBasic b G) :
    BoundaryBasic b (fun x => F x * G x) := by
  refine ⟨fun i hi x => by rw [hF.periodic i hi x, hG.periodic i hi x], ?_⟩
  intro i hi side x hx
  rw [contract_mul, mul_add, ← mul_assoc, hF.horizontal i hi side x hx, zero_mul, zero_add,
    ← mul_assoc, dx, oneForm_mul, mul_assoc]
  rw [← dx, hG.horizontal i hi side x hx, mul_zero]

theorem BoundaryBasic.one (b : BoxCycle n) : BoundaryBasic b (fun _ => (1 : Exterior n)) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩

/-- Top-degree integration over a coordinate box. -/
noncomputable def integrateTop (b : BoxCycle n) (F : Coordinates n → Exterior n) : ℝ :=
  ∫ x in Icc b.lower b.upper, topCoefficient n (F x)

theorem integrateTop_sub (b : BoxCycle n) {F G : Coordinates n → Exterior n}
    (hF : Continuous F) (hG : Continuous G) :
    integrateTop b (fun x => F x - G x) = integrateTop b F - integrateTop b G := by
  simp only [integrateTop, map_sub]
  exact integral_sub ((topCoefficient n).continuous.comp hF).integrableOn_Icc
    ((topCoefficient n).continuous.comp hG).integrableOn_Icc

theorem integrateTop_smul (b : BoxCycle n) (a : ℝ) (F : Coordinates n → Exterior n) :
    integrateTop b (fun x => a • F x) = a * integrateTop b F := by
  simp only [integrateTop, map_smul, smul_eq_mul, integral_const_mul]

theorem integrateTop_exteriorD_zero {b : BoxCycle (n + 1)}
    {F : Coordinates (n + 1) → Exterior (n + 1)} (hF : ContDiff ℝ ∞ F)
    (hb : BoundaryBasic b F) : integrateTop b (exteriorD F) = 0 := by
  rw [integrateTop, integral_exteriorD_eq_flux hF b.ordered]
  apply Finset.sum_eq_zero
  intro i _
  have hface (x : Coordinates n) :
      coordinateFlux i (F (i.insertNth (b.upper i) x)) =
        coordinateFlux i (F (i.insertNth (b.lower i) x)) := by
    by_cases hi : i ∈ b.periodic
    · have hpair : i.insertNth (b.upper i) x = i.insertNth (b.lower i) x + b.period i := by
        funext j
        rcases eq_or_ne j i with rfl | hji
        · simp [BoxCycle.period, Pi.add_apply, Pi.smul_apply]
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
          simp [BoxCycle.period, Pi.add_apply, Pi.smul_apply]
      rw [hpair, hb.periodic i hi]
    · have hzero (side : Bool) : coordinateFlux i (F (i.insertNth (b.face i side) x)) = 0 :=
        coordinateFlux_eq_zero _ (b.tangent_ne_zero i hi side) (b.tangent_normal_zero i hi side)
          (hb.horizontal i hi side _ (Fin.insertNth_apply_same _ _ _))
      rw [show b.upper i = b.face i true from rfl, show b.lower i = b.face i false from rfl,
        hzero true, hzero false]
  simp_rw [hface, sub_self]

theorem directional_on_line {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : X → Y} {x v : X}
    (hF : DifferentiableAt ℝ F x) :
    HasDerivAt (fun t : ℝ => F (x + t • v)) (directional v F x) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have hs := HasDerivAt.smul_const (hasDerivAt_id' (0 : ℝ)) v
    rw [one_smul] at hs
    exact (hasDerivAt_const_add_iff x).mpr hs
  have hF' : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • v) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt 0 hline

theorem directional_eq_of_line_eq {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F G : X → Y} {x y v : X}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G y)
    (h : ∀ t : ℝ, F (x + t • v) = G (y + t • v)) :
    directional v F x = directional v G y := by
  rw [← (directional_on_line hF).deriv, ← (directional_on_line hG).deriv, funext h]

theorem directional_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : Coordinates n → Y} (hF : Differentiable ℝ F) {v p : Coordinates n}
    (hp : ∀ x, F (x + p) = F x) (x : Coordinates n) :
    directional v F (x + p) = directional v F x := by
  apply directional_eq_of_line_eq (hF _) (hF _)
  intro t
  rw [show (x + p) + t • v = (x + t • v) + p by abel, hp]

theorem exteriorD_periodic {F : Coordinates n → Exterior n} (hF : Differentiable ℝ F)
    {p : Coordinates n} (hp : ∀ x, F (x + p) = F x) (x : Coordinates n) :
    exteriorD F (x + p) = exteriorD F x := by
  simp only [exteriorD, directional_periodic hF hp]

theorem dx_mul_congr {i : Fin n} {a a' c c' : Exterior n}
    (ha : dx i * a = dx i * a') (hc : dx i * c = dx i * c') :
    dx i * (a * c) = dx i * (a' * c') := by
  rw [← mul_assoc, ha, dx, oneForm_mul, mul_assoc, ← dx, hc, dx, ← mul_assoc,
    ← oneForm_mul, mul_assoc]

theorem on_face_add_smul {i : Fin n} {x v : Coordinates n} {c : ℝ}
    (hx : x i = c) (hv : v i = 0) (t : ℝ) :
    (x + t • v) i = c := by
  simp [Pi.add_apply, Pi.smul_apply, hx, hv]

theorem directional_congr_on_face {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F G : Coordinates n → Y} {i : Fin n} {x v : Coordinates n} {c : ℝ}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (hx : x i = c) (hv : v i = 0) (he : ∀ y, y i = c → F y = G y) :
    directional v F x = directional v G x :=
  directional_eq_of_line_eq hF hG fun t => he _ (on_face_add_smul hx hv t)

theorem dx_exteriorD_congr {F G : Coordinates n → Exterior n} {i : Fin n}
    {x : Coordinates n} {c : ℝ} (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (hx : x i = c) (he : ∀ y, y i = c → dx i * F y = dx i * G y) :
    dx i * exteriorD F x = dx i * exteriorD G x := by
  simp only [exteriorD, mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [← mul_assoc]
  · let L := exteriorMulL n (dx i)
    have hd := directional_congr_on_face
      (L.differentiableAt.comp x hF) (L.differentiableAt.comp x hG) hx
      (v := axis j) (by simp [hji]) he
    have hd' : dx i * directional (axis j) F x = dx i * directional (axis j) G x := by
      change directional (axis j) (fun y => L (F y)) x =
        directional (axis j) (fun y => L (G y)) x at hd
      rw [directional_linear hF L, directional_linear hG L] at hd
      exact hd
    rw [← mul_assoc, ← mul_assoc, dx, dx, oneForm_anticomm (axis i), neg_mul, neg_mul,
      mul_assoc, mul_assoc, ← dx]
    exact congrArg (fun a => -(dx j * a)) hd'

/-- Boundary transformation laws for a connection form of fixed phase character. -/
structure BoxConnection (b : BoxCycle n) (charge : Fin n → Bool → ℝ)
    (A : Coordinates n → Exterior n) : Prop where
  smooth : ContDiff ℝ ∞ A
  odd : ∀ x, parity (A x) = -A x
  periodic : ∀ i ∈ b.periodic, ∀ x, A (x + b.period i) = A x
  invariant : ∀ i ∉ b.periodic, ∀ side x, x i = b.face i side → ∀ t : ℝ,
    dx i * A (x + t • b.tangent i side) = dx i * A x
  evaluates : ∀ i ∉ b.periodic, ∀ side x, x i = b.face i side →
    contract (b.tangent i side) (A x) = charge i side • 1

theorem BoxConnection.curvature_basic {b : BoxCycle n} {charge : Fin n → Bool → ℝ}
    {A : Coordinates n → Exterior n} (hA : BoxConnection b charge A) :
    BoundaryBasic b (exteriorD A) := by
  have hd := hA.smooth.differentiable (by simp)
  refine ⟨fun i hi => exteriorD_periodic hd (hA.periodic i hi), ?_⟩
  intro i hi side x hx
  let v := b.tangent i side
  let L := exteriorMulL n (dx i)
  have hdir : dx i * directional v A x = 0 := by
    have hline := directional_eq_of_line_eq (L.differentiableAt.comp x (hd x))
      (differentiableAt_const (L (A x))) (x := x) (y := x) (v := v)
      (hA.invariant i hi side x hx)
    change directional v (fun y => L (A y)) x = _ at hline
    rw [directional_linear (hd x) L] at hline
    simpa [directional, L] using hline
  have hc : dx i * exteriorD (fun y => contract v (A y)) x =
      dx i * exteriorD (fun _ => charge i side • (1 : Exterior n)) x := by
    apply dx_exteriorD_congr ((contract v).differentiableAt.comp x (hd x))
      (differentiableAt_const _) hx
    intro y hy
    exact congrArg (dx i * ·) (hA.evaluates i hi side y hy)
  rw [exteriorD_const, mul_zero] at hc
  rw [contract_exteriorD v (hd x), mul_sub, hdir, hc, sub_self]

theorem BoxConnection.difference_basic {b : BoxCycle n} {charge : Fin n → Bool → ℝ}
    {A A' : Coordinates n → Exterior n} (hA : BoxConnection b charge A)
    (hA' : BoxConnection b charge A') : BoundaryBasic b (fun x => A x - A' x) := by
  refine ⟨fun i hi x => by rw [hA.periodic i hi x, hA'.periodic i hi x], ?_⟩
  intro i hi side x hx
  rw [map_sub, hA.evaluates i hi side x hx, hA'.evaluates i hi side x hx, sub_self, mul_zero]

end SymmetricMaximizer.Geometry
