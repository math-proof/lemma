import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc7_choosePeriod_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_choosePeriod_pos_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  0 < jc7_choosePeriod K hK e he := by
-- proof
  apply StatMech.Walls.jc7_choosePeriod_pos K hK e he

/--
[jc7_choosePeriod_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_choosePeriod_iterate_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  (dartNext K)^[jc7_choosePeriod K hK e he] e = e := by
-- proof
  apply StatMech.Walls.jc7_choosePeriod_iterate K hK e he

/--
[jc7_dartOrbitPeriod_dvd_choose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_dartOrbitPeriod_dvd_choose_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  dartOrbitPeriod K ⟨e, he⟩ ∣ jc7_choosePeriod K hK e he := by
-- proof
  apply StatMech.Walls.jc7_dartOrbitPeriod_dvd_choose K hK e he

/--
[jc7_choose_eq_dartOrbitPeriod_of_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_choose_eq_dartOrbitPeriod_of_injOn_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he))) :
-- imply
  jc7_choosePeriod K hK e he = dartOrbitPeriod K ⟨e, he⟩ := by
-- proof
  apply StatMech.Walls.jc7_choose_eq_dartOrbitPeriod_of_injOn K hK e he hinj

/--
[jc7_dartOrbitFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_dartOrbitFaceLoop_isCycle_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he))) :
-- imply
  (dartOrbitFaceLoop K hK e he).IsCycle := by
-- proof
  apply StatMech.Walls.jc7_dartOrbitFaceLoop_isCycle K hK e he hp hinj

/--
[jc7_LoopIsCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_LoopIsCycle_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he))) :
-- imply
  (olb_orbitLoop K hK e he).IsCycle := by
-- proof
  apply StatMech.Walls.jc7_LoopIsCycle K hK e he hp hinj

/--
[jc7_loopIsCycle_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_loopIsCycle_support_nodup_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he))) :
-- imply
  (olb_orbitLoop K hK e he).support.tail.Nodup := by
-- proof
  apply StatMech.Walls.jc7_loopIsCycle_support_nodup K hK e he hp hinj

/--
[jc7_loopIsCycle_count_support_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_loopIsCycle_count_support_of_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
  {v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he)))
  (hv : v ∈ (olb_orbitLoop K hK e he).support)
  (hvb : v ≠ dartFace e) :
-- imply
  (olb_orbitLoop K hK e he).support.count v = 1 := by
-- proof
  apply StatMech.Walls.jc7_loopIsCycle_count_support_of_mem K hK e he hp hinj hv hvb

/--
[jc7_loopIsCycle_count_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_loopIsCycle_count_support_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he))) :
-- imply
  (olb_orbitLoop K hK e he).support.count (dartFace e) = 2 := by
-- proof
  apply StatMech.Walls.jc7_loopIsCycle_count_support K hK e he hp hinj

/--
[jc7_minimalPeriod_loopIsCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_minimalPeriod_loopIsCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitLoop K a).IsCycle := by
-- proof
  apply StatMech.Walls.jc7_minimalPeriod_loopIsCycle K a hp hinj

/--
[jc7_dartOrbitWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_dartOrbitWalk_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  (dartOrbitWalk K a).IsCycle := by
-- proof
  apply StatMech.Walls.jc7_dartOrbitWalk_isCycle K hK a

/--
[jc7_unitCell_faceInj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_unitCell_faceInj_eq :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1)) (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
-- proof
  apply StatMech.Walls.jc7_unitCell_faceInj

/--
[jc7_unitCell_minimalPeriod_loopIsCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopiscycle.lean)
-/
@[path]
private lemma jc7_unitCell_minimalPeriod_loopIsCycle_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase).IsCycle := by
-- proof
  apply StatMech.Walls.jc7_unitCell_minimalPeriod_loopIsCycle


-- created on 2026-10-23
