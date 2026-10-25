import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
open SimpleGraph Function StatMech StatMech.Lattice


/--
[rot90Fun_iterate_four_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rot90Fun_iterate_four_eq_eq
  {x : Site 2} :
-- imply
  rot90Fun^[4] x = x := by
-- proof
  apply StatMech.Lattice.rot90Fun_iterate_four_eq x

/--
[rot90Fun_iterate_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rot90Fun_iterate_mod_eq
  {n : ℕ}
  {x : Site 2} :
-- imply
  rot90Fun^[n] x = rot90Fun^[n % 4] x := by
-- proof
  apply StatMech.Lattice.rot90Fun_iterate_mod n x

/--
[rotPow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rotPow_zero_eq
  {x : Site 2} :
-- imply
  rotPow 0 x = x := by
-- proof
  apply StatMech.Lattice.rotPow_zero x

/--
[rotPow_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rotPow_one_eq
  {x : Site 2} :
-- imply
  rotPow 1 x = rot90Fun x := by
-- proof
  apply StatMech.Lattice.rotPow_one x

/--
[rotPow_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rotPow_two_eq
  {x : Site 2} :
-- imply
  rotPow 2 x = -x := by
-- proof
  apply StatMech.Lattice.rotPow_two x

/--
[rotPow_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rotPow_three_eq
  {x : Site 2} :
-- imply
  rotPow 3 x = -rot90Fun x := by
-- proof
  apply StatMech.Lattice.rotPow_three x

/--
[rotPow_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rotPow_add_eq
  {a b : ZMod 4}
  {x : Site 2} :
-- imply
  rotPow (a + b) x = rotPow a (rotPow b x) := by
-- proof
  apply StatMech.Lattice.rotPow_add a b x

/--
[neg_dartDir_ne_dartDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma neg_dartDir_ne_dartDir_eq
  {e : Dart} :
-- imply
  -e.dir ≠ e.dir := by
-- proof
  apply StatMech.Lattice.neg_dartDir_ne_dartDir e

/--
[zmod4_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma zmod4_cases_eq
  {s : ZMod 4} :
-- imply
  s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
-- proof
  apply StatMech.Lattice.zmod4_cases s

/--
[rotPow_dir_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma rotPow_dir_eq_iff_eq
  {e : Dart}
  {s : ZMod 4} :
-- imply
  rotPow s e.dir = e.dir ↔ s = 0 := by
-- proof
  apply StatMech.Lattice.rotPow_dir_eq_iff e s

/--
[turnZ_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma turnZ_mem_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = 1 ∨ turnZ K e = 0 ∨ turnZ K e = -1 := by
-- proof
  apply StatMech.Lattice.turnZ_mem K e

/--
[abs_turnZ_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma abs_turnZ_le_one_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  |turnZ K e| ≤ 1 := by
-- proof
  apply StatMech.Lattice.abs_turnZ_le_one K e

/--
[turnZ_cast_eq_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma turnZ_cast_eq_turn_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  ((turnZ K e : ℤ) : ZMod 4) = turn K e := by
-- proof
  apply StatMech.Lattice.turnZ_cast_eq_turn K e

/--
[dartNext_dir_eq_rotPow_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma dartNext_dir_eq_rotPow_turn_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  (dartNext K e).dir = rotPow (turn K e) e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_dir_eq_rotPow_turn K e

/--
[cumTurn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma cumTurn_zero_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  cumTurn K e 0 = 0 := by
-- proof
  apply StatMech.Lattice.cumTurn_zero K e

/--
[cumTurn_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma cumTurn_succ_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ} :
-- imply
  cumTurn K e (k + 1) = turn K ((dartNext K)^[k] e) + cumTurn K e k := by
-- proof
  apply StatMech.Lattice.cumTurn_succ K e k

/--
[dir_iterate_eq_rotPow_cumTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma dir_iterate_eq_rotPow_cumTurn_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ} :
-- imply
  ((dartNext K)^[k] e).dir = rotPow (cumTurn K e k) e.dir := by
-- proof
  apply StatMech.Lattice.dir_iterate_eq_rotPow_cumTurn K e k

/--
[totalTurnZ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma totalTurnZ_zero_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  totalTurnZ K e 0 = 0 := by
-- proof
  apply StatMech.Lattice.totalTurnZ_zero K e

/--
[totalTurnZ_cast_eq_cumTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma totalTurnZ_cast_eq_cumTurn_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  ((totalTurnZ K e p : ℤ) : ZMod 4) = cumTurn K e p := by
-- proof
  apply StatMech.Lattice.totalTurnZ_cast_eq_cumTurn K e p

/--
[abs_totalTurnZ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma abs_totalTurnZ_le_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  |totalTurnZ K e p| ≤ (p : ℤ) := by
-- proof
  apply StatMech.Lattice.abs_totalTurnZ_le K e p

/--
[cumTurn_eq_zero_of_iterate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma cumTurn_eq_zero_of_iterate_eq_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hp : (dartNext K)^[p] e = e) :
-- imply
  cumTurn K e p = 0 := by
-- proof
  apply StatMech.Lattice.cumTurn_eq_zero_of_iterate_eq K e p hp

/--
[four_dvd_totalTurnZ_of_iterate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma four_dvd_totalTurnZ_of_iterate_eq_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hp : (dartNext K)^[p] e = e) :
-- imply
  (4 : ℤ) ∣ totalTurnZ K e p := by
-- proof
  apply StatMech.Lattice.four_dvd_totalTurnZ_of_iterate_eq K e p hp

/--
[orbit_iterate_period_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma orbit_iterate_period_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartNext K)^[dartOrbitPeriod K a] a.1 = a.1 := by
-- proof
  apply StatMech.Lattice.orbit_iterate_period_eq K a

/--
[dartOrbitPeriod_cumTurn_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma dartOrbitPeriod_cumTurn_eq_zero_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  cumTurn K a.1 (dartOrbitPeriod K a) = 0 := by
-- proof
  apply StatMech.Lattice.dartOrbitPeriod_cumTurn_eq_zero K a

/--
[four_dvd_orbit_totalTurnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma four_dvd_orbit_totalTurnZ_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.four_dvd_orbit_totalTurnZ K a

/--
[abs_orbit_totalTurnZ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma abs_orbit_totalTurnZ_le_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) := by
-- proof
  apply StatMech.Lattice.abs_orbit_totalTurnZ_le K a

/--
[orbitPeriod_ge_four_of_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean)
-/
@[path]
private lemma orbitPeriod_ge_four_of_fullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  4 ≤ dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.orbitPeriod_ge_four_of_fullRevolution K a h


-- created on 2026-10-23
