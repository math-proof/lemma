import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc4_orbitiscycle
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc4_orbitFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean)
-/
@[path]
private lemma kc4_orbitFaceLoop_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitFaceLoop K a).IsCycle := by
-- proof
  apply StatMech.Walls.kc4_orbitFaceLoop_isCycle K a hp hinj

/--
[kc4_OrbitIsCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean)
-/
@[path]
private lemma kc4_OrbitIsCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitLoop K a).IsCycle := by
-- proof
  apply StatMech.Walls.kc4_OrbitIsCycle K a hp hinj

/--
[kc4_orbitIsCycle_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean)
-/
@[path]
private lemma kc4_orbitIsCycle_support_nodup_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitLoop K a).support.tail.Nodup := by
-- proof
  apply StatMech.Walls.kc4_orbitIsCycle_support_nodup K a hp hinj

/--
[kc4_orbitIsCycle_count_support_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean)
-/
@[path]
private lemma kc4_orbitIsCycle_count_support_of_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {v : Site 2}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)))
  (hv : v ∈ (mpl_orbitLoop K a).support)
  (hvb : v ≠ dartFace a.1) :
-- imply
  (mpl_orbitLoop K a).support.count v = 1 := by
-- proof
  apply StatMech.Walls.kc4_orbitIsCycle_count_support_of_mem K a hp hinj hv hvb

/--
[kc4_orbitIsCycle_count_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean)
-/
@[path]
private lemma kc4_orbitIsCycle_count_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitLoop K a).support.count (dartFace a.1) = 2 := by
-- proof
  apply StatMech.Walls.kc4_orbitIsCycle_count_support K a hp hinj

/--
[kc4_unitCell_faceInj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean)
-/
@[path]
private lemma kc4_unitCell_faceInj_eq :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1)) (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
-- proof
  apply StatMech.Walls.kc4_unitCell_faceInj

/--
[kc4_unitCell_orbitIsCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean)
-/
@[path]
private lemma kc4_unitCell_orbitIsCycle_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase).IsCycle := by
-- proof
  apply StatMech.Walls.kc4_unitCell_orbitIsCycle


-- created on 2026-10-23
