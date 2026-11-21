module

public import SymmetricMaximizer.Boundary
import Mathlib.Tactic

/-!
# The Chern number of a sum of line bundles

On the coordinate box, the top Chern form is the ordered product of
the curvature forms of the line summands. Changing the connections
within their phase characters changes this product by an exact form
whose primitive satisfies the boundary conditions.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

variable {n m : ℕ}

/-- The exterior product of a finite ordered family of forms. -/
noncomputable def formProduct (F : Fin m → Coordinates n → Exterior n)
    (x : Coordinates n) : Exterior n :=
  (List.ofFn fun i => F i x).prod

@[simp] theorem formProduct_zero (F : Fin 0 → Coordinates n → Exterior n)
    (x : Coordinates n) : formProduct F x = 1 := by simp [formProduct]

theorem formProduct_succ (F : Fin (m + 1) → Coordinates n → Exterior n)
    (x : Coordinates n) : formProduct F x = F 0 x * formProduct (fun i : Fin m => F i.succ) x := by
  simp [formProduct, List.ofFn_succ]

theorem formProduct_eq_zero_of_component (F : Fin m → Coordinates n → Exterior n)
    {x : Coordinates n} {i : Fin m} (hi : F i x = 0) : formProduct F x = 0 := by
  rw [formProduct]
  apply List.prod_eq_zero
  rw [List.mem_ofFn]
  exact ⟨i, hi⟩

theorem exteriorD_add {F G : Coordinates n → Exterior n} {x : Coordinates n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    exteriorD (fun y => F y + G y) x = exteriorD F x + exteriorD G x := by
  simp only [exteriorD, directional, fderiv_fun_add hF hG, add_apply, mul_add,
    Finset.sum_add_distrib]

theorem exteriorD_one (x : Coordinates n) : exteriorD (fun _ => (1 : Exterior n)) x = 0 :=
  exteriorD_const 1 x

/-- A product of curvatures is smooth, closed, and satisfies the boundary conditions. -/
theorem curvatureProduct_closed {b : BoxCycle n}
    {charge : Fin m → Fin n → Bool → ℝ} {A : Fin m → Coordinates n → Exterior n}
    (hA : ∀ i, BoxConnection b (charge i) (A i)) :
    let P := formProduct (fun i => exteriorD (A i))
    ContDiff ℝ ∞ P ∧ BoundaryBasic b P ∧ ∀ x, exteriorD P x = 0 := by
  induction m with
  | zero =>
    have h : formProduct (fun i => exteriorD (A i)) = (fun _ => 1) :=
      funext (formProduct_zero _)
    rw [h]
    exact ⟨contDiff_const, BoundaryBasic.one b, exteriorD_one⟩
  | succ m ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih (fun i : Fin m => hA i.succ)
    dsimp only at h₁ h₂ h₃ ⊢
    rw [show formProduct (fun i => exteriorD (A i)) =
      (fun x => exteriorD (A 0) x * formProduct (fun i : Fin m => exteriorD (A i.succ)) x)
      from funext (formProduct_succ _)]
    let C := exteriorD (A 0)
    have hC := smooth_exteriorD (hA 0).smooth
    refine ⟨smooth_exterior_mul hC h₁, (hA 0).curvature_basic.mul h₂, fun x => ?_⟩
    rw [exteriorD_mul (hC.differentiable (by simp) x) (h₁.differentiable (by simp) x),
      exteriorD_sq (hA 0).smooth, h₃ x, zero_mul, mul_zero, add_zero]

/-- The difference of two curvature products with the same characters is exact. -/
theorem exists_transgression {b : BoxCycle n}
    {charge : Fin m → Fin n → Bool → ℝ} {A A' : Fin m → Coordinates n → Exterior n}
    (hA : ∀ i, BoxConnection b (charge i) (A i))
    (hA' : ∀ i, BoxConnection b (charge i) (A' i)) :
    ∃ K : Coordinates n → Exterior n, ContDiff ℝ ∞ K ∧ BoundaryBasic b K ∧
      ∀ x, exteriorD K x =
        formProduct (fun i => exteriorD (A i)) x - formProduct (fun i => exteriorD (A' i)) x := by
  induction m with
  | zero =>
    refine ⟨fun _ => 0, contDiff_const, ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩,
      fun x => ?_⟩
    rw [formProduct_zero, formProduct_zero, exteriorD_const, sub_self]
  | succ m ih =>
    let P := formProduct (fun i : Fin m => exteriorD (A i.succ))
    let P' := formProduct (fun i : Fin m => exteriorD (A' i.succ))
    obtain ⟨hp, hpb, hpd⟩ := curvatureProduct_closed (fun i : Fin m => hA i.succ)
    obtain ⟨K, hKs, hKb, hKd⟩ := ih (fun i : Fin m => hA i.succ) (fun i : Fin m => hA' i.succ)
    change ContDiff ℝ ∞ P at hp
    change BoundaryBasic b P at hpb
    change ∀ x, exteriorD P x = 0 at hpd
    change ∀ x, exteriorD K x = P x - P' x at hKd
    let D := fun x => A 0 x - A' 0 x
    let C' := exteriorD (A' 0)
    have hD : ContDiff ℝ ∞ D := (hA 0).smooth.sub (hA' 0).smooth
    have hC' : ContDiff ℝ ∞ C' := smooth_exteriorD (hA' 0).smooth
    have hDs := smooth_exterior_mul hD hp
    have hCs := smooth_exterior_mul hC' hKs
    refine ⟨fun x => D x * P x + C' x * K x, hDs.add hCs,
      (((hA 0).difference_basic (hA' 0)).mul hpb).add ((hA' 0).curvature_basic.mul hKb),
      fun x => ?_⟩
    rw [exteriorD_add (hDs.differentiable (by simp) x) (hCs.differentiable (by simp) x),
      exteriorD_mul (hD.differentiable (by simp) x) (hp.differentiable (by simp) x),
      exteriorD_mul (hC'.differentiable (by simp) x) (hKs.differentiable (by simp) x),
      hpd, hKd, mul_zero, add_zero]
    have hclosed : exteriorD C' x = 0 := exteriorD_sq (hA' 0).smooth x
    have heven : parity (C' x) = C' x :=
      parity_exteriorD_of_odd ((hA' 0).smooth.differentiable (by simp) x) (hA' 0).odd
    rw [hclosed, heven, zero_mul, zero_add, formProduct_succ, formProduct_succ]
    change exteriorD (fun y => A 0 y - A' 0 y) x * P x + C' x * (P x - P' x) =
      exteriorD (A 0) x * P x - C' x * P' x
    rw [exteriorD_sub ((hA 0).smooth.differentiable (by simp) x)
      ((hA' 0).smooth.differentiable (by simp) x)]
    change (exteriorD (A 0) x - C' x) * P x + C' x * (P x - P' x) = _
    rw [sub_mul, mul_sub]
    abel

/-- The Chern integral depends on the phase characters of the line bundles. -/
theorem integrateTop_curvatureProduct_eq {b : BoxCycle (n + 1)}
    {charge : Fin m → Fin (n + 1) → Bool → ℝ}
    {A A' : Fin m → Coordinates (n + 1) → Exterior (n + 1)}
    (hA : ∀ i, BoxConnection b (charge i) (A i))
    (hA' : ∀ i, BoxConnection b (charge i) (A' i)) :
    integrateTop b (formProduct (fun i => exteriorD (A i))) =
      integrateTop b (formProduct (fun i => exteriorD (A' i))) := by
  obtain ⟨K, hKs, hKb, hKd⟩ := exists_transgression hA hA'
  have hint := integrateTop_exteriorD_zero hKs hKb
  obtain ⟨h₁, _, _⟩ := curvatureProduct_closed hA
  obtain ⟨h₂, _, _⟩ := curvatureProduct_closed hA'
  have h₁' : IntegrableOn (fun x => topCoefficient _ (formProduct (fun i => exteriorD (A i)) x))
      (Icc b.lower b.upper) :=
    ((topCoefficient _).continuous.comp h₁.continuous).continuousOn.integrableOn_Icc
  have h₂' : IntegrableOn (fun x => topCoefficient _ (formProduct (fun i => exteriorD (A' i)) x))
      (Icc b.lower b.upper) :=
    ((topCoefficient _).continuous.comp h₂.continuous).continuousOn.integrableOn_Icc
  unfold integrateTop at hint ⊢
  simp_rw [hKd, map_sub] at hint
  rw [integral_sub h₁' h₂'] at hint
  exact sub_eq_zero.mp hint

end SymmetricMaximizer.Geometry
