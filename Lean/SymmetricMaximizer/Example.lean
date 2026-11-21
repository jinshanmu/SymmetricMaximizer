module

public import SymmetricMaximizer.Basic
import SymmetricMaximizer.Elimination
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic
meta import Lean.Elab.Eval

/-!
# The exact order-seven example

The matrix, basis order, and rational pivots are those in `eq:example` and `eq:bounds`.
-/

@[expose] public section

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace SymmetricMaximizer

/-- The integer matrix in equation `eq:example`. -/
def exampleSeven : Matrix (Fin 7) (Fin 7) ℤ :=
  !![  0,  80,   0,  -1,   0,   0,   7;
     -80, -20, -60,   5,   1,   0,   8;
       0, -60,  20,   4,   0,   1,   1;
       0,   7,   4, -80,  20,   0,  10;
       0,  -1,   0, -20, -40,  80, -10;
       0,   0,   1,   0, -80,  40,   0;
       7,  -6,   0,  -5,  -5,   0, -80]

/-- The manuscript's example viewed as a real matrix. -/
noncomputable def exampleSevenReal : Matrix (Fin 7) (Fin 7) ℝ := exampleSeven.map Int.cast

private def offDiagonalPairs : List (Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap fun i =>
    ((List.finRange 7).filter fun j => decide (i < j)).map fun j => (i, j)

private def basisPairs (symmetric : Bool) : List (Fin 7 × Fin 7) :=
  if symmetric then (List.finRange 7).map (fun i => (i, i)) ++ offDiagonalPairs
  else offDiagonalPairs

private def dimension (symmetric : Bool) : ℕ := if symmetric then 28 else 21

private theorem basisPairs_length (symmetric : Bool) :
    (basisPairs symmetric).length = dimension symmetric := by
  cases symmetric <;> decide

private def label (symmetric : Bool) (a : Fin (dimension symmetric)) : Fin 7 × Fin 7 :=
  (basisPairs symmetric).get (a.cast (basisPairs_length symmetric).symm)

private theorem label_injective (symmetric : Bool) : Function.Injective (label symmetric) := by
  cases symmetric <;> unfold Function.Injective <;> decide +kernel

private theorem label_mem (symmetric : Bool) : ∀ i j : Fin 7,
    (∃ a, label symmetric a = (i, j)) ↔ i < j ∨ (symmetric = true ∧ i = j) := by
  cases symmetric <;> decide +kernel

private def sign (R : Type*) [Ring R] (symmetric : Bool) : R := if symmetric then 1 else -1

private def basisMatrix (R : Type*) [Ring R] (symmetric : Bool)
    (a : Fin (dimension symmetric)) : Matrix (Fin 7) (Fin 7) R :=
  of fun i j => if (i, j) = label symmetric a then 1
    else if (j, i) = label symmetric a then sign R symmetric else 0

private theorem label_le (symmetric : Bool) (a : Fin (dimension symmetric)) :
    (label symmetric a).1 ≤ (label symmetric a).2 :=
  ((label_mem symmetric _ _).mp ⟨a, Prod.eta _⟩).elim le_of_lt (fun h => h.2.le)

private theorem basis_in_transposeClass {R : Type*} [Ring R] (symmetric : Bool)
    (a : Fin (dimension symmetric)) :
    (basisMatrix R symmetric a)ᵀ = sign R symmetric • basisMatrix R symmetric a := by
  ext i j
  by_cases hij : (i, j) = label symmetric a <;> by_cases hji : (j, i) = label symmetric a
  · have heq : i = j := congrArg Prod.fst (hij.trans hji.symm)
    have hs : symmetric = true := ((label_mem symmetric i j).mp ⟨a, hij.symm⟩).resolve_left
      (not_lt_of_ge heq.ge) |>.1
    simp [basisMatrix, hij, hji, sign, hs]
  · cases symmetric <;> simp [basisMatrix, hij, hji, sign]
  · cases symmetric <;> simp [basisMatrix, hij, hji, sign]
  · simp [basisMatrix, hij, hji]

private def linearCombination {R : Type*} [Ring R] (symmetric : Bool)
    (x : Fin (dimension symmetric) → R) : Matrix (Fin 7) (Fin 7) R :=
  ∑ a, x a • basisMatrix R symmetric a

private theorem linearCombination_transpose {R : Type*} [CommRing R] (symmetric : Bool)
    (x : Fin (dimension symmetric) → R) :
    (linearCombination symmetric x)ᵀ = sign R symmetric • linearCombination symmetric x := by
  unfold linearCombination
  rw [Matrix.transpose_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.transpose_smul, basis_in_transposeClass, smul_comm (x a)]

private theorem linearCombination_spans {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (symmetric : Bool) (X : Matrix (Fin 7) (Fin 7) R) (hX : Xᵀ = sign R symmetric • X) :
    linearCombination symmetric (fun a => X (label symmetric a).1 (label symmetric a).2) = X := by
  let Y := linearCombination symmetric (fun a => X (label symmetric a).1 (label symmetric a).2)
  have hY := linearCombination_transpose symmetric
    (fun a => X (label symmetric a).1 (label symmetric a).2)
  have upper (i j : Fin 7) (hij : i ≤ j) : Y i j = X i j := by
    by_cases hlabel : ∃ a, label symmetric a = (i, j)
    · obtain ⟨a, ha⟩ := hlabel
      unfold Y linearCombination
      rw [Matrix.sum_apply, Finset.sum_eq_single a]
      · simp [basisMatrix, ha]
      · intro b _ hba
        have hab : (i, j) ≠ label symmetric b := fun h =>
          hba (label_injective symmetric (h.symm.trans ha.symm))
        have hba' : (j, i) ≠ label symmetric b := by
          intro h
          have hji : j ≤ i := by simpa [← h] using label_le symmetric b
          exact hab (by simpa [le_antisymm hij hji] using h)
        simp [basisMatrix, hab, hba']
      · simp
    · have heq : i = j := le_antisymm hij (le_of_not_gt fun h =>
        hlabel ((label_mem symmetric i j).mpr (Or.inl h)))
      subst j
      have hs : symmetric = false := by
        cases symmetric with
        | false => rfl
        | true => exact (hlabel ((label_mem true i i).mpr (Or.inr ⟨rfl, rfl⟩))).elim
      subst symmetric
      have hz : X i i = 0 := by
        have ht := congrArg (fun M : Matrix (Fin 7) (Fin 7) R => M i i) hX
        change X i i = (-1 : R) * X i i at ht
        have ht' : (2 : R) * X i i = 0 := by linear_combination ht
        exact (mul_eq_zero.mp ht').resolve_left (by norm_num)
      unfold Y linearCombination
      rw [Matrix.sum_apply, hz]
      apply Finset.sum_eq_zero
      intro a _
      have ha : (i, i) ≠ label false a := fun h => hlabel ⟨a, h.symm⟩
      simp [basisMatrix, ha]
  ext i j
  by_cases hij : i ≤ j
  · exact upper i j hij
  · have hji := upper j i (le_of_not_ge hij)
    have htX := congrArg (fun M : Matrix (Fin 7) (Fin 7) R => M j i) hX
    have htY := congrArg (fun M : Matrix (Fin 7) (Fin 7) R => M j i) hY
    change X i j = sign R symmetric * X j i at htX
    change Y i j = sign R symmetric * Y j i at htY
    change Y i j = X i j
    rw [htY, hji, ← htX]

private def entryDot {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (X Y : Matrix ι ι R) : R := ∑ i, ∑ j, X i j * Y i j

private theorem entryDot_comm {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (X Y : Matrix ι ι R) : entryDot X Y = entryDot Y X := by
  simp only [entryDot, mul_comm]

private def gramDifference {R : Type*} [CommRing R] (A : Matrix (Fin 7) (Fin 7) R)
    (symmetric : Bool) (p q : ℕ) : Matrix (Fin (dimension symmetric)) (Fin (dimension symmetric)) R :=
  of fun i j =>
    let F := basisMatrix R symmetric
    p ^ 2 * entryDot (F i) (F j) - q ^ 2 * entryDot (lyapunov A (F i)) (lyapunov A (F j))

private theorem gramDifference_isSymm {R : Type*} [CommRing R]
    (A : Matrix (Fin 7) (Fin 7) R) (symmetric : Bool) (p q : ℕ) :
    (gramDifference A symmetric p q).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [gramDifference, of_apply, entryDot_comm (basisMatrix R symmetric j),
    entryDot_comm (lyapunov A (basisMatrix R symmetric j))]

private def rationalGram (symmetric : Bool) (p q : ℕ) :=
  gramDifference (exampleSeven.map (Int.cast : ℤ → ℚ)) symmetric p q

private abbrev RationalTable := List (List (ℤ × ℕ))

private def toTable {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : RationalTable :=
  List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => ((M i j).num, (M i j).den)

private def ofTable (n : ℕ) (table : RationalTable) : Matrix (Fin n) (Fin n) ℚ :=
  of fun i j =>
    let q := ((table[i.val]?.getD [])[j.val]?).getD (0, 1)
    mkRat q.1 q.2

private theorem ofTable_toTable {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    ofTable n (toTable M) = M := by
  ext i j
  simp [toTable, ofTable, Rat.mkRat_self]

private def pivotTables : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → List RationalTable
  | 0, _ => []
  | n + 1, M =>
    let table := toTable M
    table :: pivotTables (schur (ofTable (n + 1) table))

open Lean Elab Term in
/-- Generate candidate rational Schur tables for the kernel to check independently. -/
elab "pivot_tables% " m:term : term => do
  let candidate ← `(pivotTables $m)
  let tables ← unsafe Term.evalTerm (List RationalTable) (toTypeExpr (List RationalTable)) candidate
  return toExpr tables

private def checkFloors : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → List RationalTable → Option (List ℤ)
  | 0, _, [] => some []
  | n + 1, M, table :: rest =>
    if toTable M = table then
      let T := ofTable (n + 1) table
      (checkFloors (schur T) rest).map (fun ds => ⌊T 0 0⌋ :: ds)
    else none
  | _, _, _ => none

private theorem checkFloors_sound : {n : ℕ} →
    ∀ (M : Matrix (Fin n) (Fin n) ℚ) (tables : List RationalTable) (ds : List ℤ),
      checkFloors M tables = some ds → (pivots M).map Int.floor = ds
  | 0, _, [], _, h => by simpa [checkFloors, pivots] using h
  | 0, _, _ :: _, _, h => by simp [checkFloors] at h
  | _n + 1, _, [], _, h => by simp [checkFloors] at h
  | n + 1, M, table :: rest, ds, h => by
    rw [checkFloors] at h
    split at h
    next htable =>
      have hM : ofTable (n + 1) table = M := by rw [← htable, ofTable_toTable]
      rw [hM] at h
      cases hrest : checkFloors (schur M) rest with
      | none => simp [hrest] at h
      | some tail =>
        simp only [hrest, Option.map_some, Option.some.injEq] at h
        rw [← h, pivots, List.map_cons, checkFloors_sound (schur M) rest tail hrest]
    next _ => simp at h

private theorem gramDifference_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin 7) (Fin 7) R) (symmetric : Bool) (p q : ℕ) :
    (gramDifference A symmetric p q).map f = gramDifference (A.map f) symmetric p q := by
  have map_basis (a : Fin (dimension symmetric)) :
      (basisMatrix R symmetric a).map f = basisMatrix S symmetric a := by
    ext i j
    cases symmetric <;> simp [basisMatrix, sign, apply_ite f]
  have map_lyapunov (X : Matrix (Fin 7) (Fin 7) R) :
      (lyapunov A X).map f = lyapunov (A.map f) (X.map f) := by
    simp [lyapunov, Matrix.map_add, Matrix.map_mul, Matrix.transpose_map]
  have map_dot (X Y : Matrix (Fin 7) (Fin 7) R) :
      f (entryDot X Y) = entryDot (X.map f) (Y.map f) := by
    simp [entryDot, map_sum]
  ext i j
  simp only [gramDifference, Matrix.map_apply, of_apply, map_sub, map_mul, map_pow, map_natCast,
    map_dot, map_lyapunov, map_basis]

private theorem realGram_eq (symmetric : Bool) (p q : ℕ) :
    gramDifference exampleSevenReal symmetric p q = (rationalGram symmetric p q).map (Rat.castHom ℝ) := by
  have hA : (exampleSeven.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℝ) = exampleSevenReal := by
    ext i j
    simp [exampleSevenReal]
  rw [rationalGram, gramDifference_map, hA]

private theorem entryDot_combination {R ι : Type*} [CommRing R] [Fintype ι]
    {m : ℕ} (F : Fin m → Matrix ι ι R) (x : Fin m → R) (Y : Matrix ι ι R) :
    entryDot (∑ a, x a • F a) Y = ∑ a, x a * entryDot (F a) Y := by
  classical
  simp only [entryDot, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  calc
    _ = ∑ i, ∑ a, ∑ j, x a * (F a i j * Y i j) := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem quadratic_gramDifference {R : Type*} [Field R] (A : Matrix (Fin 7) (Fin 7) R)
    (symmetric : Bool) (p q : ℕ) (x : Fin (dimension symmetric) → R) :
    quadratic (gramDifference A symmetric p q) x =
      p ^ 2 * entryDot (linearCombination symmetric x) (linearCombination symmetric x) -
      q ^ 2 * entryDot (lyapunov A (linearCombination symmetric x))
        (lyapunov A (linearCombination symmetric x)) := by
  have double (F : Fin (dimension symmetric) → Matrix (Fin 7) (Fin 7) R) :
      entryDot (∑ a, x a • F a) (∑ a, x a • F a) =
        ∑ i, ∑ j, x i * (entryDot (F i) (F j) * x j) := by
    simp only [entryDot_combination]
    apply Finset.sum_congr rfl
    intro i _
    rw [entryDot_comm (F i), entryDot_combination, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [entryDot_comm (F j), mul_comm (x j)]
  have map_combination : lyapunov A (linearCombination symmetric x) =
      ∑ a, x a • lyapunov A (basisMatrix R symmetric a) := by
    simp only [lyapunov, linearCombination, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Finset.sum_add_distrib, smul_add]
  have factor (c : R) (f : Fin (dimension symmetric) → Fin (dimension symmetric) → R) :
      (∑ i, ∑ j, x i * (c * f i j) * x j) = c * (∑ i, ∑ j, x i * (f i j * x j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [map_combination]
  simp only [quadratic, gramDifference, of_apply, mul_sub, sub_mul, Finset.sum_sub_distrib,
    factor, linearCombination, double]

private theorem entryDot_self_real {ι : Type*} [Fintype ι] (X : Matrix ι ι ℝ) :
    entryDot X X = ‖X‖ ^ 2 := by
  simpa [frobeniusInner, entryDot] using frobeniusInner_self X

private theorem quadratic_gramDifference_real (A : Matrix (Fin 7) (Fin 7) ℝ)
    (symmetric : Bool) (p q : ℕ) (x : Fin (dimension symmetric) → ℝ) :
    quadratic (gramDifference A symmetric p q) x =
      p ^ 2 * ‖linearCombination symmetric x‖ ^ 2 -
        q ^ 2 * ‖lyapunov A (linearCombination symmetric x)‖ ^ 2 := by
  rw [quadratic_gramDifference, entryDot_self_real, entryDot_self_real]

private def symmetricFloors : List ℤ :=
  [1421529, 381503, 1125046, 548722, 958895, 318216, 567764, 631968, 2527713,
    2750225, 2579602, 2373148, 2301303, 720504, 1270362, 672834, 668103, 1378914,
    799487, 1335181, 1401196, 1108367, 909801, 1082451, 524117, 130009, 485800, 1024128]

private def skewFloors : List ℤ :=
  [248170, 197521, 174448, 162019, 148812, 175510, 222494, 111254, 43232, 43259,
    108137, 144845, 90979, 96483, 116956, 87678, 177840, 17610, 276194, 56865, -9319]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem symmetricFloors_eq : (pivots (rationalGram true 1499 8)).map Int.floor = symmetricFloors := by
  apply checkFloors_sound _ (pivot_tables% (rationalGram true 1499 8))
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem skewFloors_eq : (pivots (rationalGram false 375 2)).map Int.floor = skewFloors := by
  apply checkFloors_sound _ (pivot_tables% (rationalGram false 375 2))
  decide +kernel

private theorem symmetricPivots_pos :
    ∀ d ∈ pivots (gramDifference exampleSevenReal true 1499 8), 0 < d := by
  rw [realGram_eq, pivots_map]
  intro d hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
  have hf : ⌊q⌋ ∈ symmetricFloors := symmetricFloors_eq ▸ List.mem_map_of_mem hq
  have hcheck : symmetricFloors.all (fun z => decide (0 < z)) = true := by decide
  have hpos : 0 < ⌊q⌋ := of_decide_eq_true (List.all_eq_true.mp hcheck _ hf)
  have hqpos : 0 < q := (show (0 : ℚ) < ↑⌊q⌋ by exact_mod_cast hpos).trans_le (Int.floor_le q)
  change (0 : ℝ) < (q : ℝ)
  exact_mod_cast hqpos

private theorem skewPivots_ne_zero :
    ∀ d ∈ pivots (gramDifference exampleSevenReal false 375 2), d ≠ 0 := by
  rw [realGram_eq, pivots_map]
  intro d hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
  have hf : ⌊q⌋ ∈ skewFloors := skewFloors_eq ▸ List.mem_map_of_mem hq
  have hcheck : skewFloors.all (fun z => decide (z ≠ 0)) = true := by decide
  have hne : ⌊q⌋ ≠ 0 := of_decide_eq_true (List.all_eq_true.mp hcheck _ hf)
  have hqne : q ≠ 0 := fun h => hne (by simp [h])
  change (q : ℝ) ≠ 0
  exact_mod_cast hqne

private theorem skewPivots_exists_neg :
    ∃ d ∈ pivots (gramDifference exampleSevenReal false 375 2), d < 0 := by
  rw [realGram_eq, pivots_map]
  have hlast : (-9319 : ℤ) ∈ skewFloors := by decide
  rw [← skewFloors_eq] at hlast
  obtain ⟨q, hq, hfloor⟩ := List.mem_map.mp hlast
  refine ⟨q, List.mem_map_of_mem (f := Rat.castHom ℝ) hq, ?_⟩
  have hlt : q < (⌊q⌋ : ℚ) + 1 := Int.lt_floor_add_one q
  rw [hfloor] at hlt
  have hqneg : q < 0 := hlt.trans (by norm_num)
  change (q : ℝ) < 0
  exact_mod_cast hqneg

private theorem symmetricNorm_exampleSeven_lt : symmetricNorm exampleSevenReal < 1499 / 8 := by
  by_contra! h
  have hp : 0 < symmetricNorm exampleSevenReal := by linarith
  obtain ⟨X, hX, hLX⟩ := exists_unit_attains_of_pos (restricted 1 exampleSevenReal) hp
  change ‖(X : Matrix (Fin 7) (Fin 7) ℝ)‖ = 1 at hX
  change ‖lyapunov exampleSevenReal X‖ = symmetricNorm exampleSevenReal at hLX
  let x := fun a => (X : Matrix (Fin 7) (Fin 7) ℝ) (label true a).1 (label true a).2
  have hspan : linearCombination true x = (X : Matrix (Fin 7) (Fin 7) ℝ) :=
    linearCombination_spans true (X : Matrix (Fin 7) (Fin 7) ℝ) X.property
  have hx : x ≠ 0 := by
    intro heq
    rw [← hspan, heq] at hX
    simp [linearCombination] at hX
  have hq := quadratic_pos_of_pivots (gramDifference_isSymm exampleSevenReal true 1499 8)
    symmetricPivots_pos x hx
  rw [quadratic_gramDifference_real, hspan, hX, hLX] at hq
  have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1499 / 8) hp.le).mpr h
  norm_num at hq hs
  linarith

private theorem lt_skewNorm_exampleSeven : 375 / 2 < skewNorm exampleSevenReal := by
  obtain ⟨x, hx⟩ := exists_quadratic_neg_of_pivots
    (gramDifference_isSymm exampleSevenReal false 375 2) skewPivots_ne_zero skewPivots_exists_neg
  rw [quadratic_gramDifference_real] at hx
  let X := linearCombination false x
  have hsq : ((375 / 2 : ℝ) * ‖X‖) ^ 2 < ‖lyapunov exampleSevenReal X‖ ^ 2 := by
    change (375 : ℝ) ^ 2 * ‖X‖ ^ 2 - 2 ^ 2 * ‖lyapunov exampleSevenReal X‖ ^ 2 < 0 at hx
    rw [mul_pow]
    norm_num at hx ⊢
    linarith
  have hlt := (sq_lt_sq₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 375 / 2) (norm_nonneg X))
    (norm_nonneg _)).mp hsq
  exact lt_of_mul_lt_mul_right
    (hlt.trans_le (lyapunov_le (-1) exampleSevenReal X (linearCombination_transpose false x)))
    (norm_nonneg _)

/-- The two exact rational bounds in equation `eq:bounds`. -/
theorem exampleSeven_bounds : symmetricNorm exampleSevenReal < 1499 / 8 ∧
    (1499 / 8 : ℝ) < 375 / 2 ∧ 375 / 2 < skewNorm exampleSevenReal :=
  ⟨symmetricNorm_exampleSeven_lt, by norm_num, lt_skewNorm_exampleSeven⟩

end SymmetricMaximizer
