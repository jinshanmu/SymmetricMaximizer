module

public import SymmetricMaximizer.ProjectiveConnections
public import SymmetricMaximizer.EvenForms
import Mathlib.Tactic

/-!
# Orientation of the curvature product

The base curvature already uses all three base phase directions.
Consequently the relative phase connections can be replaced by the
two fiber phase covectors when extracting the oriented top coefficient.
-/

@[expose] public section

open Set.powersetCard
open scoped BigOperators

namespace SymmetricMaximizer.Geometry

/-- The product of all coordinate covectors in increasing order. -/
noncomputable def orientedVolume (n : ℕ) : Exterior n :=
  (List.ofFn (fun i : Fin n => dx i)).prod

theorem orientedVolume_eq_basis (n : ℕ) :
    orientedVolume n = exteriorBasis n Finset.univ := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  let full : Set.powersetCard (Fin n) n := ofCard hcard
  have horder :
      (⇑(ofFinEmbEquiv.symm full) : Fin n → Fin n) = id := by
    rw [ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique hcard (fun _ => Finset.mem_univ _) strictMono_id).symm
  rw [exteriorBasis, ExteriorAlgebra.basis_apply_ofCard _ hcard]
  change orientedVolume n = ExteriorAlgebra.ιMulti_family ℝ n (Pi.basisFun ℝ (Fin n)) full
  rw [ExteriorAlgebra.ιMulti_family, horder, Function.comp_id, ExteriorAlgebra.ιMulti_apply]
  simp [orientedVolume, dx, axis]

@[simp] theorem topCoefficient_orientedVolume (n : ℕ) :
    topCoefficient n (orientedVolume n) = 1 := by
  simp [orientedVolume_eq_basis, topCoefficient_basis]

private noncomputable def baseVolume : Exterior 10 :=
  (dx 0 * dx 1) * (dx 2 * dx 3) * (dx 4 * dx 5)

private theorem dxpair_center (i j : Fin 10) :
    dx i * dx j ∈ Subalgebra.center ℝ (Exterior 10) :=
  mem_center_of_even (parity_two_covectors _ _)

private theorem baseVolume_kills (k : Fin 3) :
    baseVolume * dx (phaseIndex (basePair k)) = 0 := by
  have hc₁ := (Subalgebra.mem_center_iff.mp (dxpair_center 0 1))
  have hc₂ := (Subalgebra.mem_center_iff.mp (dxpair_center 2 3))
  fin_cases k
  · change ((dx 0 * dx 1) * (dx 2 * dx 3) * (dx 4 * dx 5)) * dx 1 = 0
    calc
      _ = (dx 0 * dx 1) * ((dx 2 * dx 3) * (dx 4 * dx 5)) * dx 1 := by
        simp [mul_assoc]
      _ = ((dx 2 * dx 3) * (dx 4 * dx 5)) * ((dx 0 * dx 1) * dx 1) := by
        rw [← hc₁ ((dx 2 * dx 3) * (dx 4 * dx 5))]
        simp [mul_assoc]
      _ = 0 := by rw [mul_assoc (dx 0), dx_sq, mul_zero, mul_zero]
  · change ((dx 0 * dx 1) * (dx 2 * dx 3) * (dx 4 * dx 5)) * dx 3 = 0
    calc
      _ = ((dx 0 * dx 1) * (dx 4 * dx 5)) * ((dx 2 * dx 3) * dx 3) := by
        rw [mul_assoc (dx 0 * dx 1), ← hc₂ (dx 4 * dx 5)]
        simp [mul_assoc]
      _ = 0 := by rw [mul_assoc (dx 2), dx_sq, mul_zero, mul_zero]
  · change ((dx 0 * dx 1) * (dx 2 * dx 3) * (dx 4 * dx 5)) * dx 5 = 0
    rw [mul_assoc, mul_assoc (dx 4), dx_sq, mul_zero, mul_zero]

private theorem baseVolume_kills_connection (k : Fin 3) (x : Coordinates 10) :
    baseVolume * baseConnection k x = 0 := by
  rw [baseConnection, mul_smul_comm, baseVolume_kills, smul_zero]

private theorem baseVolume_dx_kills_connection (i : Fin 10) (k : Fin 3) (x : Coordinates 10) :
    baseVolume * (dx i * baseConnection k x) = 0 := by
  rw [dx, oneForm_mul, (baseConnection_laws k).odd x, neg_mul, mul_neg,
    ← mul_assoc, baseVolume_kills_connection, zero_mul, neg_zero]

private theorem dx_anticomm (i j : Fin 10) : dx i * dx j = -(dx j * dx i) :=
  oneForm_anticomm _ _

private theorem fiber_volume_product (r : ℝ) :
    (dx (n := 10) 6 * ((1 - r) • dx 7 + r • dx 9)) * (dx 8 * (dx 9 - dx 7)) =
      (dx 6 * dx 7) * (dx 8 * dx 9) := by
  have h₇ : (dx (n := 10) 6 * dx 7) * (dx 8 * dx 7) = 0 := by
    rw [mul_assoc (dx 6), ← mul_assoc (dx 7), dx_anticomm 7 8, neg_mul, mul_assoc (dx 8),
      dx_sq, mul_zero, neg_zero, mul_zero]
  have h₉ : (dx (n := 10) 6 * dx 9) * (dx 8 * dx 9) = 0 := by
    rw [mul_assoc (dx 6), ← mul_assoc (dx 9), dx_anticomm 9 8, neg_mul, mul_assoc (dx 8),
      dx_sq, mul_zero, neg_zero, mul_zero]
  have hswap : (dx (n := 10) 6 * dx 9) * (dx 8 * dx 7) = -((dx 6 * dx 7) * (dx 8 * dx 9)) := by
    calc
      _ = dx 6 * ((dx 9 * dx 8) * dx 7) := by simp [mul_assoc]
      _ = -((dx 6 * dx 8) * (dx 9 * dx 7)) := by rw [dx_anticomm 9 8]; noncomm_ring
      _ = (dx 6 * dx 8) * (dx 7 * dx 9) := by rw [dx_anticomm 9 7]; noncomm_ring
      _ = _ := by
        rw [mul_assoc (dx 6), ← mul_assoc (dx 8), dx_anticomm 8 7]
        noncomm_ring
  simp only [mul_add, add_mul, mul_sub, mul_smul_comm, smul_mul_assoc, h₇, h₉, hswap]
  module

/-- Product of the three base curvatures and the fiber volume contribution. -/
theorem volume_product (x : Coordinates 10) :
    (baseCurvature 0 x * baseCurvature 1 x * baseCurvature 2 x) *
      (2 * (tautFiber₁ x * tautFiber₂ x)) =
      ((polarAreaDeriv 0 x * polarAreaDeriv 1 x * polarAreaDeriv 2 x) *
        (2 * (polarAreaDeriv 3 x * (polarArea 3 x * polarAreaDeriv 4 x)))) •
          orientedVolume 10 := by
  let u := dx 6 * fiberAngle x
  let v := dx 8 * (fiberAngle₂ x - fiberAngle₁ x)
  let u' : Exterior 10 := dx 6 * ((1 - polarArea 4 x) • dx 7 + polarArea 4 x • dx 9)
  let v' : Exterior 10 := dx 8 * (dx 9 - dx 7)
  have hu : baseVolume * u = baseVolume * u' := by
    dsimp only [u, u', fiberAngle, fiberAngle₁, fiberAngle₂]
    simp only [mul_add, mul_sub, mul_smul_comm, baseVolume_dx_kills_connection]
    module
  have hv : baseVolume * v = baseVolume * v' := by
    dsimp only [v, v', fiberAngle₁, fiberAngle₂]
    simp [mul_add, mul_sub, baseVolume_dx_kills_connection]
  have hu' : u' ∈ Subalgebra.center ℝ (Exterior 10) := by
    apply mem_center_of_even
    dsimp only [u']
    simp only [map_mul, map_smul, map_add, dx, parity_oneForm, smul_neg, ← neg_add, neg_mul_neg]
  have ht : baseVolume * (u * v) = orientedVolume 10 := by
    rw [← mul_assoc, hu, Subalgebra.mem_center_iff.mp hu' baseVolume, mul_assoc, hv,
      ← mul_assoc, ← Subalgebra.mem_center_iff.mp hu' baseVolume, mul_assoc]
    change baseVolume * ((dx 6 * ((1 - polarArea 4 x) • dx 7 + polarArea 4 x • dx 9)) *
      (dx 8 * (dx 9 - dx 7))) = _
    rw [fiber_volume_product]
    simp [orientedVolume, List.ofFn_succ, baseVolume, mul_assoc]
  change ((polarAreaDeriv 0 x • (dx 0 * dx 1)) * (polarAreaDeriv 1 x • (dx 2 * dx 3)) *
    (polarAreaDeriv 2 x • (dx 4 * dx 5))) *
      (2 * ((polarAreaDeriv 3 x • u) * ((polarArea 3 x * polarAreaDeriv 4 x) • v))) = _
  rw [two_mul, ← two_smul ℝ]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  change _ • (baseVolume * (u * v)) = _
  rw [ht]
  module

end SymmetricMaximizer.Geometry
