import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc6_singlecycle.Part2
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc6_orbit_injOn_Iio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_orbit_injOn_Iio_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (fun k => (dartNextSub K)^[k] a) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Walls.jc6_orbit_injOn_Iio K a

/--
[jc6_iterate_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_iterate_eq_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {j k : ℕ}
-- given
  (hj : j < dartOrbitPeriod K a)
  (hk : k < dartOrbitPeriod K a) :
-- imply
  (dartNextSub K)^[j] a = (dartNextSub K)^[k] a ↔ j = k := by
-- proof
  apply StatMech.Walls.jc6_iterate_eq_iff K a hj hk

/--
[jc6_orbit_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_orbit_distinct_eq
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
  apply StatMech.Walls.jc6_orbit_distinct K a hj hk hjk

/--
[jc6_no_dart_recurs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_no_dart_recurs_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {d : {e : Dart // IsBoundaryDart K e}}
  {j k : ℕ}
-- given
  (hj : j < dartOrbitPeriod K a)
  (hk : k < dartOrbitPeriod K a)
  (hjd : (dartNextSub K)^[j] a = d)
  (hkd : (dartNextSub K)^[k] a = d) :
-- imply
  j = k := by
-- proof
  apply StatMech.Walls.jc6_no_dart_recurs K a hj hk hjd hkd

/--
[jc6_recur_step_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_recur_step_injOn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {d : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (id : ℕ → ℕ) {k | k ∈ Set.Iio (dartOrbitPeriod K a) ∧ (dartNextSub K)^[k] a = d} := by
-- proof
  apply StatMech.Walls.jc6_recur_step_injOn K a d

/--
[jc6_recur_step_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_recur_step_subsingleton_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {d : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Subsingleton {k : ℕ // k < dartOrbitPeriod K a ∧ (dartNextSub K)^[k] a = d} := by
-- proof
  apply StatMech.Walls.jc6_recur_step_subsingleton K a d

/--
[jc6_no_lframe_dart_recurs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_no_lframe_dart_recurs_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {d : {e : Dart // IsBoundaryDart K e}}
  {j k : ℕ}
-- given
  (_hd : jc5_ProbesEarFootprint r d.1)
  (hj : j < dartOrbitPeriod K a)
  (hk : k < dartOrbitPeriod K a)
  (hjd : (dartNextSub K)^[j] a = d)
  (hkd : (dartNextSub K)^[k] a = d) :
-- imply
  j = k := by
-- proof
  apply StatMech.Walls.jc6_no_lframe_dart_recurs K a r _hd hj hk hjd hkd

/--
[jc6_lframe_recur_step_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_lframe_recur_step_subsingleton_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {d : {e : Dart // IsBoundaryDart K e}}
-- given
  (_hd : jc5_ProbesEarFootprint r d.1) :
-- imply
  Subsingleton {k : ℕ // k < dartOrbitPeriod K a ∧ (dartNextSub K)^[k] a = d} := by
-- proof
  apply StatMech.Walls.jc6_lframe_recur_step_subsingleton K a r _hd

/--
[jc6_orbit_injOn_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_orbit_injOn_range_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (fun k => (dartNextSub K)^[k] a) (Finset.range (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Walls.jc6_orbit_injOn_range K a

/--
[jc6_orbit_darts_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_orbit_darts_nodup_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ((List.range (dartOrbitPeriod K a)).map (fun k => (dartNextSub K)^[k] a)).Nodup := by
-- proof
  apply StatMech.Walls.jc6_orbit_darts_nodup K a

/--
[jc6_period_darts_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_period_darts_card_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  letI : DecidableEq {e : Dart // IsBoundaryDart K e} := Classical.decEq _ ((Finset.range (dartOrbitPeriod K a)).image (fun k => (dartNextSub K)^[k] a)).card = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc6_period_darts_card K a

/--
[jc6_dartOrbitWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_dartOrbitWalk_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  (dartOrbitWalk K a).IsCycle := by
-- proof
  apply StatMech.Walls.jc6_dartOrbitWalk_isCycle K hK a

/--
[jc6_singleCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean)
-/
@[path]
private lemma jc6_singleCycle_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  jc6_SingleCycle K := by
-- proof
  apply StatMech.Walls.jc6_singleCycle K hK


-- created on 2026-10-23
