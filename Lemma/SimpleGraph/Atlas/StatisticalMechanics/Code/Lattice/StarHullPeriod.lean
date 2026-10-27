import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.StarHullPeriod
open SimpleGraph Function Set Finset StatMech StatMech.Lattice


/--
[shp_rot90_dir_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_rot90_dir_ne_eq
  {e : Dart} :
-- imply
  rot90Fun e.dir ≠ e.dir := by
-- proof
  apply StatMech.Lattice.shp_rot90_dir_ne e

/--
[shp_neg_rot90_dir_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_neg_rot90_dir_ne_eq
  {e : Dart} :
-- imply
  (-rot90Fun e.dir : Site 2) ≠ e.dir := by
-- proof
  apply StatMech.Lattice.shp_neg_rot90_dir_ne e

/--
[shp_neg_rot90_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_neg_rot90_ne_zero_eq
  {e : Dart} :
-- imply
  (-rot90Fun e.dir : Site 2) ≠ 0 := by
-- proof
  apply StatMech.Lattice.shp_neg_rot90_ne_zero e

/--
[shp_neg_dir_ne_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_neg_dir_ne_dir_eq
  {e : Dart} :
-- imply
  (-e.dir : Site 2) ≠ e.dir := by
-- proof
  apply StatMech.Lattice.shp_neg_dir_ne_dir e

/--
[shp_dir_add_t_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_dir_add_t_ne_zero_eq
  {e : Dart} :
-- imply
  e.dir + (-rot90Fun e.dir) ≠ 0 := by
-- proof
  apply StatMech.Lattice.shp_dir_add_t_ne_zero e

/--
[shp_two_t_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_two_t_ne_zero_eq
  {e : Dart} :
-- imply
  (-rot90Fun e.dir) + (-rot90Fun e.dir) ≠ (0 : Site 2) := by
-- proof
  apply StatMech.Lattice.shp_two_t_ne_zero e

/--
[shp_t_sub_dir_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_t_sub_dir_ne_zero_eq
  {e : Dart} :
-- imply
  (-rot90Fun e.dir) + (-e.dir) ≠ (0 : Site 2) := by
-- proof
  apply StatMech.Lattice.shp_t_sub_dir_ne_zero e

/--
[shp_neg_rot90_neg_rot90](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_neg_rot90_neg_rot90_eq
  {e : Dart} :
-- imply
  (-rot90Fun (-rot90Fun e.dir) : Site 2) = -e.dir := by
-- proof
  apply StatMech.Lattice.shp_neg_rot90_neg_rot90 e

/--
[shp_two_step_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_two_step_ne_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  (dartNext K)^[2] e ≠ e := by
-- proof
  apply StatMech.Lattice.shp_two_step_ne K e

/--
[shp_period_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_period_ne_two_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  dartOrbitPeriod K a ≠ 2 := by
-- proof
  apply StatMech.Lattice.shp_period_ne_two K a

/--
[shp_period_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_period_ge_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  3 ≤ dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.shp_period_ge_three K hK a

/--
[shp_starHull_period_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_starHull_period_ge_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite) :
-- imply
  3 ≤ dartOrbitPeriod (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shp_starHull_period_ge_three K hK a

/--
[shp_starHull_period_ge_three'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_starHull_period_ge_three'_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite) :
-- imply
  3 ≤ dartOrbitPeriod (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shp_starHull_period_ge_three' K hSK a

/--
[shp_starHull_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_starHull_orbit_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite) :
-- imply
  ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle := by
-- proof
  apply StatMech.Lattice.shp_starHull_orbit_isCycle K hK a

/--
[shp_box_period_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_box_period_ge_three_eq
  {n : ℕ}
  {a : {e : Dart // IsBoundaryDart (box 2 n) e}} :
-- imply
  3 ≤ dartOrbitPeriod (box 2 n) a := by
-- proof
  apply StatMech.Lattice.shp_box_period_ge_three n a

/--
[shp_box_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_box_orbit_isCycle_eq
  {n : ℕ}
  {a : {e : Dart // IsBoundaryDart (box 2 n) e}} :
-- imply
  ((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl (by rw [orbit_iterate_period_eq (box 2 n) a])).IsCycle := by
-- proof
  apply StatMech.Lattice.shp_box_orbit_isCycle n a

/--
[shp_unitCell_period_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_unitCell_period_ge_three_eq :
-- imply
  3 ≤ dartOrbitPeriod unitCell ucBase := by
-- proof
  apply StatMech.Lattice.shp_unitCell_period_ge_three

/--
[shp_domino_period_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullPeriod.lean)
-/
@[path]
private lemma shp_domino_period_ge_three_eq :
-- imply
  3 ≤ dartOrbitPeriod domino dmBase := by
-- proof
  apply StatMech.Lattice.shp_domino_period_ge_three


-- created on 2026-10-23
