import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc8cyclenodup
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc8_loopIsCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_loopIsCycle_eq
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
  apply StatMech.Walls.jc8_loopIsCycle K hK e he hp hinj

/--
[jc8_count_one_of_tail_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_count_one_of_tail_nodup_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u : V}
  {p : G.Walk u u}
  {v : V}
-- given
  (htail : p.support.tail.Nodup)
  (hv : v ∈ p.support)
  (hvu : v ≠ u) :
-- imply
  p.support.count v = 1 := by
-- proof
  apply StatMech.Walls.jc8_count_one_of_tail_nodup p htail hv hvu

/--
[jc8_tail_nodup_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_tail_nodup_of_count_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u : V}
  {p : G.Walk u u}
-- given
  (hu : p.support.count u = 2)
  (hother : ∀ v ∈ p.support, v ≠ u → p.support.count v = 1) :
-- imply
  p.support.tail.Nodup := by
-- proof
  apply StatMech.Walls.jc8_tail_nodup_of_count p hu hother

/--
[jc8_support_tail_nodup_iff_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_support_tail_nodup_iff_count_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u : V}
  {p : G.Walk u u}
-- given
  (hu : p.support.count u = 2) :
-- imply
  p.support.tail.Nodup ↔ ∀ v ∈ p.support, v ≠ u → p.support.count v = 1 := by
-- proof
  apply StatMech.Walls.jc8_support_tail_nodup_iff_count p hu

/--
[jc8_loopIsCycle_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_loopIsCycle_support_nodup_eq
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
  apply StatMech.Walls.jc8_loopIsCycle_support_nodup K hK e he hp hinj

/--
[jc8_loopIsCycle_count_support_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_loopIsCycle_count_support_of_mem_eq
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
  apply StatMech.Walls.jc8_loopIsCycle_count_support_of_mem K hK e he hp hinj hv hvb

/--
[jc8_loopIsCycle_count_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_loopIsCycle_count_support_eq
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
  apply StatMech.Walls.jc8_loopIsCycle_count_support K hK e he hp hinj

/--
[jc8_loop_support_tail_nodup_iff_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_loop_support_tail_nodup_iff_count_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he))) :
-- imply
  (olb_orbitLoop K hK e he).support.tail.Nodup ↔ ∀ v ∈ (olb_orbitLoop K hK e he).support, v ≠ dartFace e → (olb_orbitLoop K hK e he).support.count v = 1 := by
-- proof
  apply StatMech.Walls.jc8_loop_support_tail_nodup_iff_count K hK e he hp hinj

/--
[jc8_contour_face_ne_basepoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_contour_face_ne_basepoint_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he)))
  (hn0 : 0 < n)
  (hnp : n < jc7_choosePeriod K hK e he) :
-- imply
  dartFace ((dartNext K)^[n] e) ≠ dartFace e := by
-- proof
  apply StatMech.Walls.jc8_contour_face_ne_basepoint K hK e he hinj hn0 hnp

/--
[jc8_contour_face_count_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_contour_face_count_eq_one_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he)))
  (hn0 : 0 < n)
  (hnp : n < jc7_choosePeriod K hK e he) :
-- imply
  (olb_orbitLoop K hK e he).support.count (dartFace ((dartNext K)^[n] e)) = 1 := by
-- proof
  apply StatMech.Walls.jc8_contour_face_count_eq_one K hK e he hp hinj hn0 hnp

/--
[jc8_minimalPeriod_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_minimalPeriod_support_nodup_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitLoop K a).support.tail.Nodup := by
-- proof
  apply StatMech.Walls.jc8_minimalPeriod_support_nodup K a hp hinj

/--
[jc8_unitCell_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8cyclenodup.lean)
-/
@[path]
private lemma jc8_unitCell_support_nodup_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase).support.tail.Nodup := by
-- proof
  apply StatMech.Walls.jc8_unitCell_support_nodup


-- created on 2026-10-23
