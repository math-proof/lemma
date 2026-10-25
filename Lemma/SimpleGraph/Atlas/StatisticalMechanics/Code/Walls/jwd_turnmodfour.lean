import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jwd_turnmodfour
open SimpleGraph Function StatMech StatMech.Walls


/--
[jwd_cumTurn_eq_zero_of_closes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_cumTurn_eq_zero_of_closes_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hclose : (dartNext K)^[p] e = e) :
-- imply
  cumTurn K e p = 0 := by
-- proof
  apply StatMech.Walls.jwd_cumTurn_eq_zero_of_closes K e p hclose

/--
[jwd_four_dvd_totalTurn_of_closes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_four_dvd_totalTurn_of_closes_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hclose : (dartNext K)^[p] e = e) :
-- imply
  (4 : ℤ) ∣ totalTurnZ K e p := by
-- proof
  apply StatMech.Walls.jwd_four_dvd_totalTurn_of_closes K e p hclose

/--
[jwd_four_dvd_orbit_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_four_dvd_orbit_totalTurn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Walls.jwd_four_dvd_orbit_totalTurn K a

/--
[jwd_orbit_cumTurn_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_orbit_cumTurn_eq_zero_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  cumTurn K a.1 (dartOrbitPeriod K a) = 0 := by
-- proof
  apply StatMech.Walls.jwd_orbit_cumTurn_eq_zero K a

/--
[jwd_orbit_turn_eq_four_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_orbit_turn_eq_four_mul_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ∃ k : ℤ, totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * k := by
-- proof
  apply StatMech.Walls.jwd_orbit_turn_eq_four_mul K a

/--
[jwd_starHull_four_dvd_orbit_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_starHull_four_dvd_orbit_totalTurn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  (4 : ℤ) ∣ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) := by
-- proof
  apply StatMech.Walls.jwd_starHull_four_dvd_orbit_totalTurn K a

/--
[jwd_box_four_dvd_orbit_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_box_four_dvd_orbit_totalTurn_eq
  {n : ℕ}
  {a : {e : Dart // IsBoundaryDart (box 2 n) e}} :
-- imply
  (4 : ℤ) ∣ totalTurnZ (box 2 n) a.1 (dartOrbitPeriod (box 2 n) a) := by
-- proof
  apply StatMech.Walls.jwd_box_four_dvd_orbit_totalTurn n a

/--
[jwd_four_dvd_of_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_turnmodfour.lean)
-/
@[path]
private lemma jwd_four_dvd_of_fullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Walls.jwd_four_dvd_of_fullRevolution K a h


-- created on 2026-10-23
