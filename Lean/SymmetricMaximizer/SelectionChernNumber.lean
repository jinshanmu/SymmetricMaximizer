module

public import SymmetricMaximizer.PolarIntegration
public import SymmetricMaximizer.VolumeCoefficient
public import SymmetricMaximizer.ChernObstruction
public import SymmetricMaximizer.ProjectiveFrame
import SymmetricMaximizer.ChernCalculation
import Mathlib.Tactic

/-!
# The Chern number of the selection bundle

The product of the five line curvatures is the form
`(h - t)^2 (t + h₁)(t + h₂)(t + h₃)`.
The tautological inclusion supplies an exact primitive for
`(t - h₁)(t - h₂)(t - h₃)`. The polynomial reduction from the manuscript
leaves only the fiber integral of `-4 h₁ h₂ h₃ t²`.
-/

@[expose] public section

open scoped BigOperators ContDiff

namespace SymmetricMaximizer.Geometry

/-- Product of the five line curvatures in the selection bundle. -/
noncomputable def selectionChernForm (x : Coordinates 10) : Exterior 10 :=
  formProduct (fun j => exteriorD (selectionConnection j)) x

private theorem exteriorD_determinantConnection (x : Coordinates 10) :
    exteriorD determinantConnection x = baseCurvature 0 x + baseCurvature 1 x +
      baseCurvature 2 x - exteriorD tautConnection x := by
  have h₀ := (baseConnection_laws 0).smooth.differentiable (by simp) x
  have h₁ := (baseConnection_laws 1).smooth.differentiable (by simp) x
  have h₂ := (baseConnection_laws 2).smooth.differentiable (by simp) x
  have ht := tautConnection_laws.smooth.differentiable (by simp) x
  have h₀₁ : DifferentiableAt ℝ (fun y => baseConnection 0 y + baseConnection 1 y) x :=
    h₀.add h₁
  have hsum : DifferentiableAt ℝ
      (fun y => baseConnection 0 y + baseConnection 1 y + baseConnection 2 y) x :=
    h₀₁.add h₂
  unfold determinantConnection
  rw [exteriorD_sub hsum ht, exteriorD_add h₀₁ h₂, exteriorD_add h₀ h₁]
  simp only [exteriorD_baseConnection]

theorem selectionChernForm_polynomial (x : Coordinates 10) :
    let a := baseCurvature 0 x
    let b := baseCurvature 1 x
    let c := baseCurvature 2 x
    let t := exteriorD tautConnection x
    (selectionChernForm x) = (a + b + c - t) ^ 2 * ((t + a) * (t + b) * (t + c)) := by
  let a := baseCurvature 0 x
  let b := baseCurvature 1 x
  let c := baseCurvature 2 x
  let t := exteriorD tautConnection x
  let D := a + b + c - t
  have hfirst (j : Fin 5) (hj : j.val < 3) :
      exteriorD (selectionConnection j) x = t + baseCurvature ⟨j.val, hj⟩ x := by
    have he : selectionConnection j =
        (fun y => tautConnection y + baseConnection ⟨j.val, hj⟩ y) :=
      funext fun y => by simp [selectionConnection, hj]
    rw [he, exteriorD_add (tautConnection_laws.smooth.differentiable (by simp) x)
      ((baseConnection_laws _).smooth.differentiable (by simp) x), exteriorD_baseConnection]
  have hlast (j : Fin 5) (hj : ¬j.val < 3) : exteriorD (selectionConnection j) x = D := by
    have he : selectionConnection j = determinantConnection :=
      funext fun y => by simp [selectionConnection, hj]
    rw [he, exteriorD_determinantConnection]
  have hprod : selectionChernForm x = (t + a) * ((t + b) * ((t + c) * (D * D))) := by
    unfold selectionChernForm formProduct
    norm_num [List.ofFn_succ]
    rw [hfirst 0 (by decide), hfirst 1 (by decide), hfirst 2 (by decide),
      hlast 3 (by decide), hlast 4 (by decide)]
    rfl
  have hD : D ∈ Subalgebra.center ℝ (Exterior 10) := by
    rw [← hlast 3 (by decide)]
    exact mem_center_of_even (parity_exteriorD_of_odd
      ((selectionConnection_laws 3).smooth.differentiable (by simp) x)
      (selectionConnection_laws 3).odd)
  change selectionChernForm x = D ^ 2 * ((t + a) * (t + b) * (t + c))
  calc
    selectionChernForm x = ((t + a) * (t + b) * (t + c)) * D ^ 2 := by
      simp only [hprod, pow_two, mul_assoc]
    _ = _ := Subalgebra.mem_center_iff.mp
      ((Subalgebra.center ℝ (Exterior 10)).pow_mem hD 2) _

private theorem twoForm_mem_and_sq {n : ℕ} (s : ℝ) (v w : Coordinates n) :
    let a := s • (oneForm v * oneForm w)
    a ∈ Subalgebra.center ℝ (Exterior n) ∧ a ^ 2 = 0 := by
  refine ⟨mem_center_of_even (by rw [map_smul, parity_two_covectors]), ?_⟩
  rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two (oneForm v * oneForm w),
    two_covectors_sq, smul_zero]

private theorem baseCurvature_mem_and_sq (i : Fin 3) (x : Coordinates 10) :
    baseCurvature i x ∈ Subalgebra.center ℝ (Exterior 10) ∧ baseCurvature i x ^ 2 = 0 :=
  twoForm_mem_and_sq _ _ _

private theorem baseConnection_in_range (i : Fin 3) (x : Coordinates 10) :
    baseConnection i x ∈ LinearMap.range (oneForm (n := 10)) := by
  exact ⟨polarArea (basePair i) x • axis (phaseIndex (basePair i)), map_smul _ _ _⟩

private theorem fiberAngle₁_in_range (x : Coordinates 10) :
    fiberAngle₁ x ∈ LinearMap.range (oneForm (n := 10)) := by
  exact Submodule.add_mem _ (Submodule.sub_mem _ (baseConnection_in_range 1 x)
    (baseConnection_in_range 0 x)) (LinearMap.mem_range_self _ _)

private theorem fiberAngle₂_in_range (x : Coordinates 10) :
    fiberAngle₂ x ∈ LinearMap.range (oneForm (n := 10)) := by
  exact Submodule.add_mem _ (Submodule.sub_mem _ (baseConnection_in_range 2 x)
    (baseConnection_in_range 0 x)) (LinearMap.mem_range_self _ _)

private theorem tautFiber₁_mem_and_sq (x : Coordinates 10) :
    tautFiber₁ x ∈ Subalgebra.center ℝ (Exterior 10) ∧ tautFiber₁ x ^ 2 = 0 := by
  have h : fiberAngle x ∈ LinearMap.range (oneForm (n := 10)) :=
    Submodule.add_mem _ (fiberAngle₁_in_range x) (Submodule.smul_mem _ _
      (Submodule.sub_mem _ (fiberAngle₂_in_range x) (fiberAngle₁_in_range x)))
  obtain ⟨v, hv⟩ := h
  rw [tautFiber₁, ← hv]
  exact twoForm_mem_and_sq _ _ _

private theorem tautFiber₂_mem_and_sq (x : Coordinates 10) :
    tautFiber₂ x ∈ Subalgebra.center ℝ (Exterior 10) ∧ tautFiber₂ x ^ 2 = 0 := by
  have h : fiberAngle₂ x - fiberAngle₁ x ∈ LinearMap.range (oneForm (n := 10)) :=
    Submodule.sub_mem _ (fiberAngle₂_in_range x) (fiberAngle₁_in_range x)
  obtain ⟨v, hv⟩ := h
  rw [tautFiber₂, ← hv]
  exact twoForm_mem_and_sq _ _ _

private noncomputable def inclusionConnection (i : Fin 3) (x : Coordinates 10) : Exterior 10 :=
  tautConnection x - baseConnection i x

private theorem inclusionConnection_laws (i : Fin 3) : BoxConnection projectiveBox
    (fun j side => tautCharge j side - baseCharge i j side) (inclusionConnection i) :=
  tautConnection_laws.sub (baseConnection_laws i)

private theorem inclusionCoefficients_laws : PhaseSection projectiveBox
    (fun i j side => tautCharge j side - baseCharge i j side) (fun i x => tautCoefficients x i) := by
  refine ⟨smooth_tautCoefficient, ?_, tautCoefficients_equivariant⟩
  intro i hi j x
  rw [tautCoefficients_periodic i hi]

/-- The tautological inclusion is nowhere zero, so `∏ (t - hᵢ)` is exact. -/
theorem tautological_inclusion_exact :
    ∃ K : Coordinates 10 → Exterior 10, ContDiff ℝ ∞ K ∧ BoundaryBasic projectiveBox K ∧
      exteriorD K = fun x =>
        let t := exteriorD tautConnection x
        (t - baseCurvature 0 x) * (t - baseCurvature 1 x) * (t - baseCurvature 2 x) := by
  have hnonzero (x : Coordinates 10) : ∃ i, tautCoefficients x i ≠ 0 := by
    by_contra! h
    have hn := tautCoefficients_normSq x
    simp [h] at hn
  obtain ⟨K, hs, hb, hK⟩ := exact_curvatureProduct_of_nonvanishing_section
    inclusionConnection_laws inclusionCoefficients_laws hnonzero
  refine ⟨K, hs, hb, hK.trans (funext fun x => ?_)⟩
  have hC (i : Fin 3) : exteriorD (inclusionConnection i) x =
      exteriorD tautConnection x - baseCurvature i x := by
    unfold inclusionConnection
    rw [exteriorD_sub (tautConnection_laws.smooth.differentiable (by simp) x)
      ((baseConnection_laws i).smooth.differentiable (by simp) x), exteriorD_baseConnection]
  norm_num [formProduct, List.ofFn_succ, hC, mul_assoc]

private noncomputable def baseSumConnection (x : Coordinates 10) : Exterior 10 :=
  baseConnection 0 x + baseConnection 1 x + baseConnection 2 x

private theorem baseSumConnection_laws : BoxConnection projectiveBox
    (fun j side => baseCharge 0 j side + baseCharge 1 j side + baseCharge 2 j side)
    baseSumConnection :=
  ((baseConnection_laws 0).add (baseConnection_laws 1)).add (baseConnection_laws 2)

private theorem exteriorD_baseSumConnection (x : Coordinates 10) :
    exteriorD baseSumConnection x = baseCurvature 0 x + baseCurvature 1 x + baseCurvature 2 x := by
  have h₀ := (baseConnection_laws 0).smooth.differentiable (by simp) x
  have h₁ := (baseConnection_laws 1).smooth.differentiable (by simp) x
  have h₂ := (baseConnection_laws 2).smooth.differentiable (by simp) x
  have h₀₁ : DifferentiableAt ℝ (fun y => baseConnection 0 y + baseConnection 1 y) x := h₀.add h₁
  unfold baseSumConnection
  rw [exteriorD_add h₀₁ h₂, exteriorD_add h₀ h₁]
  simp only [exteriorD_baseConnection]

private theorem tautCurvature_mem_center (x : Coordinates 10) :
    exteriorD tautConnection x ∈ Subalgebra.center ℝ (Exterior 10) :=
  mem_center_of_even (parity_exteriorD_of_odd
    (tautConnection_laws.smooth.differentiable (by simp) x) tautConnection_laws.odd)

private theorem selectionChernForm_reduce (x : Coordinates 10) :
    let a := baseCurvature 0 x
    let b := baseCurvature 1 x
    let c := baseCurvature 2 x
    let t := exteriorD tautConnection x
    selectionChernForm x - (-4 : ℝ) • ((a * b * c) * t ^ 2) =
      (t ^ 2 - (a + b + c) ^ 2) * ((t - a) * (t - b) * (t - c)) := by
  let S := Subalgebra.center ℝ (Exterior 10)
  let a : S := ⟨baseCurvature 0 x, (baseCurvature_mem_and_sq 0 x).1⟩
  let b : S := ⟨baseCurvature 1 x, (baseCurvature_mem_and_sq 1 x).1⟩
  let c : S := ⟨baseCurvature 2 x, (baseCurvature_mem_and_sq 2 x).1⟩
  let t : S := ⟨exteriorD tautConnection x, tautCurvature_mem_center x⟩
  have ha : a ^ 2 = 0 := Subtype.ext (baseCurvature_mem_and_sq 0 x).2
  have hb : b ^ 2 = 0 := Subtype.ext (baseCurvature_mem_and_sq 1 x).2
  have hc : c ^ 2 = 0 := Subtype.ext (baseCurvature_mem_and_sq 2 x).2
  have h := topChern_polynomial_reduce a b c t ha hb hc
  have he := congrArg (fun y : S => (y : Exterior 10)) h
  change ((a : Exterior 10) + b + c - t) ^ 2 *
      ((t + a) * (t + b) * (t + c)) =
    ((t : Exterior 10) ^ 2 - (a + b + c) ^ 2) * ((t - a) * (t - b) * (t - c)) -
      4 * ((a : Exterior 10) * b * c) * (t : Exterior 10) ^ 2 at he
  dsimp only
  rw [selectionChernForm_polynomial, he, neg_smul]
  have hscale : (4 : ℝ) • ((baseCurvature 0 x * baseCurvature 1 x * baseCurvature 2 x) *
      (exteriorD tautConnection x) ^ 2) =
      4 * ((a : Exterior 10) * b * c) * (t : Exterior 10) ^ 2 := by
    rw [Algebra.smul_def, map_ofNat]
    exact (mul_assoc _ _ _).symm
  rw [hscale]
  change _ = ((t : Exterior 10) ^ 2 - (a + b + c) ^ 2) * ((t - a) * (t - b) * (t - c))
  abel

/-- The representative of `e₃ t²`, where `e₃` is the product of the three base classes. -/
noncomputable def baseVolumeTimesTautSquare (x : Coordinates 10) : Exterior 10 :=
  (baseCurvature 0 x * baseCurvature 1 x * baseCurvature 2 x) * (exteriorD tautConnection x) ^ 2

private theorem square_under_base_volume {S : Type*} [CommRing S] (a b c u v A B C : S)
    (ha : a ^ 2 = 0) (hb : b ^ 2 = 0) (hc : c ^ 2 = 0) (hu : u ^ 2 = 0) (hv : v ^ 2 = 0) :
    (a * b * c) * (A * a + B * b + C * c + u + v) ^ 2 = (a * b * c) * (2 * (u * v)) := by
  let r := A * a + B * b + C * c
  let e := a * b * c
  have hr : e * r = 0 := by
    dsimp only [e, r]
    linear_combination A * b * c * ha + B * a * c * hb + C * a * b * hc
  change e * (r + u + v) ^ 2 = e * (2 * (u * v))
  linear_combination (r + 2 * u + 2 * v) * hr + e * hu + e * hv

private theorem baseVolumeTimesTautSquare_eq (x : Coordinates 10) :
    baseVolumeTimesTautSquare x = polarVolumeDensity x • orientedVolume 10 := by
  let S := Subalgebra.center ℝ (Exterior 10)
  let a : S := ⟨baseCurvature 0 x, (baseCurvature_mem_and_sq 0 x).1⟩
  let b : S := ⟨baseCurvature 1 x, (baseCurvature_mem_and_sq 1 x).1⟩
  let c : S := ⟨baseCurvature 2 x, (baseCurvature_mem_and_sq 2 x).1⟩
  let u : S := ⟨tautFiber₁ x, (tautFiber₁_mem_and_sq x).1⟩
  let v : S := ⟨tautFiber₂ x, (tautFiber₂_mem_and_sq x).1⟩
  let A := algebraMap ℝ S (1 - polarArea 3 x)
  let B := algebraMap ℝ S (polarArea 3 x * (1 - polarArea 4 x))
  let C := algebraMap ℝ S (polarArea 3 x * polarArea 4 x)
  let t := A * a + B * b + C * c + u + v
  have ha : a ^ 2 = 0 := Subtype.ext (baseCurvature_mem_and_sq 0 x).2
  have hb : b ^ 2 = 0 := Subtype.ext (baseCurvature_mem_and_sq 1 x).2
  have hc : c ^ 2 = 0 := Subtype.ext (baseCurvature_mem_and_sq 2 x).2
  have hu : u ^ 2 = 0 := Subtype.ext (tautFiber₁_mem_and_sq x).2
  have hv : v ^ 2 = 0 := Subtype.ext (tautFiber₂_mem_and_sq x).2
  have hsq := square_under_base_volume a b c u v A B C ha hb hc hu hv
  have ht : (t : Exterior 10) = exteriorD tautConnection x := by
    rw [exteriorD_tautConnection]
    change (algebraMap ℝ (Exterior 10) (1 - polarArea 3 x) * baseCurvature 0 x +
      algebraMap ℝ (Exterior 10) (polarArea 3 x * (1 - polarArea 4 x)) * baseCurvature 1 x +
      algebraMap ℝ (Exterior 10) (polarArea 3 x * polarArea 4 x) * baseCurvature 2 x +
      tautFiber₁ x + tautFiber₂ x) = _
    simp only [← Algebra.smul_def]
  have h := congrArg (fun w : S => (w : Exterior 10)) hsq
  change ((a : Exterior 10) * b * c) * (t : Exterior 10) ^ 2 =
    ((a : Exterior 10) * b * c) * (2 * ((u : Exterior 10) * v)) at h
  rw [ht] at h
  unfold baseVolumeTimesTautSquare
  rw [h, volume_product]
  rfl

/-- The normalized integral of `e₃ t²` is one. The fiber push of the square
contributes one, and the product of the three base areas has integral one. -/
theorem integral_baseVolumeTimesTautSquare :
    integrateTop projectiveBox baseVolumeTimesTautSquare = (2 * Real.pi) ^ 5 := by
  simp only [integrateTop, baseVolumeTimesTautSquare_eq, map_smul, topCoefficient_orientedVolume,
    smul_eq_mul, mul_one]
  exact integral_polarVolumeDensity

private theorem selectionChernForm_exact_difference :
    ∃ Q : Coordinates 10 → Exterior 10, ContDiff ℝ ∞ Q ∧ BoundaryBasic projectiveBox Q ∧
      exteriorD Q = fun x => selectionChernForm x - (-4 : ℝ) • baseVolumeTimesTautSquare x := by
  obtain ⟨K, hKs, hKb, hKd⟩ := tautological_inclusion_exact
  let T := exteriorD tautConnection
  let H := exteriorD baseSumConnection
  let M := fun x => T x * T x - H x * H x
  have hT := smooth_exteriorD tautConnection_laws.smooth
  have hH := smooth_exteriorD baseSumConnection_laws.smooth
  have hT₂ := smooth_exterior_mul hT hT
  have hH₂ := smooth_exterior_mul hH hH
  have hM : ContDiff ℝ ∞ M := hT₂.sub hH₂
  have hMb : BoundaryBasic projectiveBox M :=
    (tautConnection_laws.curvature_basic.mul tautConnection_laws.curvature_basic).sub
      (baseSumConnection_laws.curvature_basic.mul baseSumConnection_laws.curvature_basic)
  have hsquare {A : Coordinates 10 → Exterior 10} (hA : ContDiff ℝ ∞ A) (x : Coordinates 10) :
      exteriorD (fun y => exteriorD A y * exteriorD A y) x = 0 := by
    have hd := (smooth_exteriorD hA).differentiable (by simp) x
    rw [exteriorD_mul hd hd, exteriorD_sq hA, zero_mul, mul_zero, add_zero]
  have hMd (x : Coordinates 10) : exteriorD M x = 0 := by
    unfold M T H
    rw [exteriorD_sub (hT₂.differentiable (by simp) x) (hH₂.differentiable (by simp) x),
      hsquare tautConnection_laws.smooth, hsquare baseSumConnection_laws.smooth, sub_self]
  have hMeven (x : Coordinates 10) : parity (M x) = M x := by
    have hTe : parity (T x) = T x := parity_exteriorD_of_odd
      (tautConnection_laws.smooth.differentiable (by simp) x) tautConnection_laws.odd
    have hHe : parity (H x) = H x := parity_exteriorD_of_odd
      (baseSumConnection_laws.smooth.differentiable (by simp) x) baseSumConnection_laws.odd
    simp only [M, map_sub, map_mul, hTe, hHe]
  refine ⟨fun x => M x * K x, smooth_exterior_mul hM hKs, hMb.mul hKb, funext fun x => ?_⟩
  rw [exteriorD_mul (hM.differentiable (by simp) x) (hKs.differentiable (by simp) x), hMd x,
    hMeven x, zero_mul, zero_add, hKd]
  unfold M T H
  rw [exteriorD_baseSumConnection, ← pow_two, ← pow_two]
  exact (selectionChernForm_reduce x).symm

/-- The top Chern integral before dividing by the five phase periods. -/
theorem integral_selectionChernForm :
    integrateTop projectiveBox selectionChernForm = -4 * (2 * Real.pi) ^ 5 := by
  obtain ⟨Q, hQs, hQb, hQd⟩ := selectionChernForm_exact_difference
  have hz := integrateTop_exteriorD_zero hQs hQb
  obtain ⟨hs, _, _⟩ := curvatureProduct_closed selectionConnection_laws
  have hvol : Continuous (fun x => (-4 : ℝ) • baseVolumeTimesTautSquare x) := by
    have HT := smooth_exteriorD tautConnection_laws.smooth
    have HB (i : Fin 3) : ContDiff ℝ ∞ (baseCurvature i) := by
      rw [← funext (exteriorD_baseConnection i)]
      exact smooth_exteriorD (baseConnection_laws i).smooth
    have hcont := smooth_exterior_mul (smooth_exterior_mul (HB 0) (HB 1)) (HB 2)
    have ht := smooth_exterior_mul HT HT
    simp only [baseVolumeTimesTautSquare, pow_two]
    exact (smooth_exterior_mul hcont ht).continuous.const_smul (-4 : ℝ)
  have hC : Continuous selectionChernForm := hs.continuous
  rw [hQd, integrateTop_sub projectiveBox hC hvol, integrateTop_smul,
    integral_baseVolumeTimesTautSquare] at hz
  exact sub_eq_zero.mp hz

/-- The normalized top Chern number of the bundle in the selection lemma. -/
theorem selectionChernNumber :
    integrateTop projectiveBox selectionChernForm / (2 * Real.pi) ^ 5 = -4 := by
  rw [integral_selectionChernForm, mul_div_cancel_right₀]
  positivity

end SymmetricMaximizer.Geometry
