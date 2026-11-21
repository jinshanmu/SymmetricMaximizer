module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic

/-!
# Exterior calculus in rectangular coordinates

We use the finite-dimensional exterior algebra on the coordinate covectors.
This gives the exterior derivative, contraction, and the identities needed
for the Chern forms on the projective flag space.
-/

@[expose] public section

open Module Finset
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

/-- Real rectangular coordinates. -/
abbrev Coordinates (n : ℕ) := Fin n → ℝ

/-- Inhomogeneous exterior forms at a point of rectangular coordinate space. -/
abbrev Exterior (n : ℕ) := ExteriorAlgebra ℝ (Coordinates n)

/-- The exterior basis of increasing products of coordinate covectors. -/
noncomputable def exteriorBasis (n : ℕ) : Basis (Finset (Fin n)) ℝ (Exterior n) :=
  (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra

noncomputable instance (n : ℕ) : NormedAddCommGroup (Exterior n) :=
  NormedAddCommGroup.induced _ _ (exteriorBasis n).equivFun (exteriorBasis n).equivFun.injective

noncomputable instance (n : ℕ) : NormedSpace ℝ (Exterior n) :=
  NormedSpace.induced ℝ _ _ (exteriorBasis n).equivFun

instance (n : ℕ) : FiniteDimensional ℝ (Exterior n) := Module.Finite.of_basis (exteriorBasis n)

variable {n : ℕ}

/-- The unit vector in a rectangular coordinate direction. -/
noncomputable def axis (i : Fin n) : Coordinates n := Pi.single i 1

@[simp] theorem axis_apply (i j : Fin n) : axis i j = if i = j then 1 else 0 := by
  simp [axis, Pi.single_apply, eq_comm]

theorem sum_axis (v : Coordinates n) : ∑ i, v i • axis i = v := by
  ext i
  simp [Pi.smul_apply]

/-- Inclusion of a coordinate covector into the exterior algebra. -/
abbrev oneForm : Coordinates n →ₗ[ℝ] Exterior n := ExteriorAlgebra.ι ℝ

/-- The covector of a coordinate direction. -/
noncomputable def dx (i : Fin n) : Exterior n := oneForm (axis i)

@[simp] theorem dx_sq (i : Fin n) : dx i * dx i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem oneForm_anticomm (v w : Coordinates n) :
    oneForm v * oneForm w = -(oneForm w * oneForm v) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v w)

/-- The parity automorphism acts by the sign of the degree. -/
abbrev parity : Exterior n →ₐ[ℝ] Exterior n :=
  CliffordAlgebra.involute (Q := (0 : QuadraticForm ℝ (Coordinates n)))

theorem parity_oneForm (v : Coordinates n) : parity (oneForm v) = -oneForm v :=
  CliffordAlgebra.involute_ι v

theorem oneForm_mul (v : Coordinates n) (a : Exterior n) :
    oneForm v * a = parity a * oneForm v := by
  induction a using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact (Algebra.commutes r _).symm
  | ι w => rw [parity_oneForm, neg_mul, oneForm_anticomm]
  | mul a b ha hb => rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]

/-- The directional derivative of a map between real normed spaces. -/
noncomputable def directional {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (v : X) (F : X → Y) (x : X) : Y :=
  fderiv ℝ F x v

theorem directional_linear {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : X → Y} {x v : X} (hF : DifferentiableAt ℝ F x) (L : Y →L[ℝ] Z) :
    directional v (fun y => L (F y)) x = L (directional v F x) := by
  have h := L.hasFDerivAt.comp x hF.hasFDerivAt
  exact congrArg (fun T : X →L[ℝ] Z => T v) h.fderiv

theorem smooth_directional {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : X → Y} (hF : ContDiff ℝ ∞ F) (v : X) :
    ContDiff ℝ ∞ (directional v F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

/-- Coordinate expression of the exterior derivative. -/
noncomputable def exteriorD (F : Coordinates n → Exterior n) (x : Coordinates n) : Exterior n :=
  ∑ i, dx i * directional (axis i) F x

/-- Continuous bilinear multiplication of coordinate exterior forms. -/
noncomputable def exteriorMulL (n : ℕ) : Exterior n →L[ℝ] Exterior n →L[ℝ] Exterior n :=
  (LinearMap.mul ℝ (Exterior n)).toContinuousBilinearMap

@[simp] theorem exteriorMulL_apply (a b : Exterior n) : exteriorMulL n a b = a * b := rfl

theorem smooth_exterior_mul {F G : Coordinates n → Exterior n}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => F x * G x) := by
  exact (exteriorMulL n).isBoundedBilinearMap.contDiff.comp₂ hF hG

theorem directional_exterior_mul {F G : Coordinates n → Exterior n} {x v : Coordinates n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    directional v (fun y => F y * G y) x =
      directional v F x * G x + F x * directional v G x := by
  let m := (exteriorMulL n).isBoundedBilinearMap
  have h := (m.hasFDerivAt (F x, G x)).comp x (hF.hasFDerivAt.prodMk hG.hasFDerivAt)
  have heq := congrArg (fun T : Coordinates n →L[ℝ] Exterior n => T v) h.fderiv
  change directional v (fun y => F y * G y) x = _ at heq
  simpa [m, IsBoundedBilinearMap.deriv, directional, add_comm] using heq

theorem smooth_exteriorD {F : Coordinates n → Exterior n} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (exteriorD F) := by
  exact ContDiff.sum fun i _ => smooth_exterior_mul contDiff_const (smooth_directional hF (axis i))

theorem exteriorD_mul {F G : Coordinates n → Exterior n} {x : Coordinates n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    exteriorD (fun y => F y * G y) x =
      exteriorD F x * G x + parity (F x) * exteriorD G x := by
  simp only [exteriorD, directional_exterior_mul hF hG, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  · exact Finset.sum_congr rfl fun i _ => by rw [← mul_assoc, dx, oneForm_mul,
      mul_assoc]

theorem exteriorD_sub {F G : Coordinates n → Exterior n} {x : Coordinates n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    exteriorD (fun y => F y - G y) x = exteriorD F x - exteriorD G x := by
  simp only [exteriorD, directional, fderiv_fun_sub hF hG, sub_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem exteriorD_sq {F : Coordinates n → Exterior n} (hF : ContDiff ℝ ∞ F) (x : Coordinates n) :
    exteriorD (exteriorD F) x = 0 := by
  have hd (i : Fin n) : ContDiff ℝ ∞ (directional (axis i) F) := smooth_directional hF _
  have hfirst (i : Fin n) :
      directional (axis i) (exteriorD F) x =
        ∑ j, dx j * directional (axis i) (directional (axis j) F) x := by
    unfold directional exteriorD
    rw [fderiv_fun_sum fun j _ =>
      (smooth_exterior_mul (F := fun _ => dx j) contDiff_const (hd j)).differentiable (by simp) x]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact directional_linear ((hd j).differentiable (by simp) x) (exteriorMulL n (dx j))
  have hsym (i j : Fin n) :
      directional (axis i) (directional (axis j) F) x =
        directional (axis j) (directional (axis i) F) x := by
    have hFd := (hF.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiable (by simp) x
    rw [show directional (axis i) (directional (axis j) F) x =
        fderiv ℝ (fderiv ℝ F) x (axis i) (axis j) from
      directional_linear hFd (ContinuousLinearMap.apply ℝ (Exterior n) (axis j))]
    rw [show directional (axis j) (directional (axis i) F) x =
        fderiv ℝ (fderiv ℝ F) x (axis j) (axis i) from
      directional_linear hFd (ContinuousLinearMap.apply ℝ (Exterior n) (axis i))]
    exact hF.contDiffAt.isSymmSndFDerivAt (by simp) _ _
  simp only [exteriorD, hfirst, mul_sum, ← mul_assoc]
  set S := ∑ i : Fin n, ∑ j : Fin n, (dx i * dx j) *
    directional (axis i) (directional (axis j) F) x
  have hS : S = -S := by
    unfold S
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i, dx, dx, oneForm_anticomm (axis j), neg_mul]
  have htwo : (2 : ℝ) • S = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hS
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end SymmetricMaximizer.Geometry
