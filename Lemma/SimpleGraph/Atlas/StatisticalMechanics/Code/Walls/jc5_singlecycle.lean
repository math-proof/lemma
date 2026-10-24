import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc5_singlecycle
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc5_orbit_injOn_Iio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_orbit_injOn_Iio_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (fun k => (dartNextSub K)^[k] a) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Walls.jc5_orbit_injOn_Iio K a

/--
[jc5_visited_once](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_visited_once_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {j k : ℕ}
-- given
  (hj : j < dartOrbitPeriod K a)
  (hk : k < dartOrbitPeriod K a) :
-- imply
  (dartNextSub K)^[j] a = (dartNextSub K)^[k] a ↔ j = k := by
-- proof
  apply StatMech.Walls.jc5_visited_once K a hj hk

/--
[jc5_orbit_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_orbit_distinct_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {j k : ℕ}
-- given
  (hj : j < dartOrbitPeriod K a)
  (hk : k < dartOrbitPeriod K a)
  (hjk : j ≠ k) :
-- imply
  (dartNextSub K)^[j] a ≠ (dartNextSub K)^[k] a := by
-- proof
  apply StatMech.Walls.jc5_orbit_distinct K a hj hk hjk

/--
[jc5_orbit_injOn_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_orbit_injOn_range_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (fun k => (dartNextSub K)^[k] a) (Finset.range (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Walls.jc5_orbit_injOn_range K a

/--
[jc5_orbit_darts_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_orbit_darts_nodup_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ((List.range (dartOrbitPeriod K a)).map (fun k => (dartNextSub K)^[k] a)).Nodup := by
-- proof
  apply StatMech.Walls.jc5_orbit_darts_nodup K a

/--
[jc5_orbit_darts_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_orbit_darts_card_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  letI : DecidableEq {e : Dart // IsBoundaryDart K e} := Classical.decEq _ ((Finset.range (dartOrbitPeriod K a)).image (fun k => (dartNextSub K)^[k] a)).card = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc5_orbit_darts_card K a

/--
[jc5_dartOrbitWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_dartOrbitWalk_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  (dartOrbitWalk K a).IsCycle := by
-- proof
  apply StatMech.Walls.jc5_dartOrbitWalk_isCycle K hK a

/--
[jc5_dartOrbitWalk_support_tail_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_dartOrbitWalk_support_tail_nodup_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  (dartOrbitWalk K a).support.tail.Nodup := by
-- proof
  apply StatMech.Walls.jc5_dartOrbitWalk_support_tail_nodup K hK a

/--
[jc5_singleCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean)
-/
@[path]
private lemma jc5_singleCycle_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  jc5_SingleCycle K := by
-- proof
  apply StatMech.Walls.jc5_singleCycle K hK


-- created on 2026-10-23
