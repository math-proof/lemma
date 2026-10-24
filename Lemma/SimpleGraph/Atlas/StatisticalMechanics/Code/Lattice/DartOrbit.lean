import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartOrbit
open SimpleGraph Function StatMech StatMech.Lattice


/--
[dartDir_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartDir_ne_zero_eq
  {e : Dart} :
-- imply
  e.dir ≠ 0 := by
-- proof
  apply StatMech.Lattice.dartDir_ne_zero e

/--
[rot90Fun_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma rot90Fun_zero_eq :
-- imply
  rot90Fun (0 : Site 2) = 0 := by
-- proof
  apply StatMech.Lattice.rot90Fun_zero

/--
[rot90Fun_dartDir_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma rot90Fun_dartDir_ne_zero_eq
  {e : Dart} :
-- imply
  rot90Fun e.dir ≠ 0 := by
-- proof
  apply StatMech.Lattice.rot90Fun_dartDir_ne_zero e

/--
[neg_rot90Fun_dartDir_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma neg_rot90Fun_dartDir_ne_zero_eq
  {e : Dart} :
-- imply
  (-rot90Fun e.dir : Site 2) ≠ 0 := by
-- proof
  apply StatMech.Lattice.neg_rot90Fun_dartDir_ne_zero e

/--
[rot90Fun_dartDir_ne_dartDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma rot90Fun_dartDir_ne_dartDir_eq
  {e : Dart} :
-- imply
  rot90Fun e.dir ≠ e.dir := by
-- proof
  apply StatMech.Lattice.rot90Fun_dartDir_ne_dartDir e

/--
[neg_rot90Fun_dartDir_ne_dartDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma neg_rot90Fun_dartDir_ne_dartDir_eq
  {e : Dart} :
-- imply
  -rot90Fun e.dir ≠ e.dir := by
-- proof
  apply StatMech.Lattice.neg_rot90Fun_dartDir_ne_dartDir e

/--
[dartNext_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartNext_ne_self_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (_he : IsBoundaryDart K e) :
-- imply
  dartNext K e ≠ e := by
-- proof
  apply StatMech.Lattice.dartNext_ne_self K e _he

/--
[dartNext_consecutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartNext_consecutive_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  ((dartNext K e).head = e.head) ∨ ((dartNext K e).tail = e.tail + (-rot90Fun e.dir) ∧ (dartNext K e).head = e.head + (-rot90Fun e.dir)) ∨ ((dartNext K e).tail = e.tail) := by
-- proof
  apply StatMech.Lattice.dartNext_consecutive K e

/--
[dartNextSub_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartNextSub_val_eq
  {K : Set (Site 2)}
  {e : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartNextSub K e).1 = dartNext K e.1 := by
-- proof
  apply StatMech.Lattice.dartNextSub_val K e

/--
[dartNextSub_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartNextSub_injective_eq
  {K : Set (Site 2)} :
-- imply
  Function.Injective (dartNextSub K) := by
-- proof
  apply StatMech.Lattice.dartNextSub_injective K

/--
[dartNextSub_iterate_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartNextSub_iterate_val_eq
  {K : Set (Site 2)}
  {e : {e : Dart // IsBoundaryDart K e}}
  {k : ℕ} :
-- imply
  ((dartNextSub K)^[k] e).1 = (dartNext K)^[k] e.1 := by
-- proof
  apply StatMech.Lattice.dartNextSub_iterate_val K e k

/--
[dartNextSub_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartNextSub_ne_self_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  dartNextSub K a ≠ a := by
-- proof
  apply StatMech.Lattice.dartNextSub_ne_self K a

/--
[dartNext_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartNext_periodic_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  ∃ p > 0, (dartNext K)^[p] e = e := by
-- proof
  apply StatMech.Lattice.dartNext_periodic K hK e he

/--
[dartSuccGraph_adj_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartSuccGraph_adj_next_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartSuccGraph K).Adj a (dartNextSub K a) := by
-- proof
  apply StatMech.Lattice.dartSuccGraph_adj_next K a

/--
[orbitWalkAux_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma orbitWalkAux_length_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ} :
-- imply
  (orbitWalkAux K a n).length = n := by
-- proof
  apply StatMech.Lattice.orbitWalkAux_length K a n

/--
[orbitWalkAux_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma orbitWalkAux_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ} :
-- imply
  (orbitWalkAux K a n).support = (List.range (n + 1)).map (fun k => (dartNextSub K)^[k] a) := by
-- proof
  apply StatMech.Lattice.orbitWalkAux_support K a n

/--
[dartOrbitPeriod_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartOrbitPeriod_pos_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  0 < dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.dartOrbitPeriod_pos K hK a

/--
[one_lt_dartOrbitPeriod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma one_lt_dartOrbitPeriod_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  1 < dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.one_lt_dartOrbitPeriod K hK a

/--
[dartOrbitPeriod_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartOrbitPeriod_iterate_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartNextSub K)^[dartOrbitPeriod K a] a = a := by
-- proof
  apply StatMech.Lattice.dartOrbitPeriod_iterate K a

/--
[dartOrbitWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartOrbitWalk_length_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartOrbitWalk K a).length = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.dartOrbitWalk_length K a

/--
[dartOrbitWalk_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartOrbitWalk_length_pos_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  0 < (dartOrbitWalk K a).length := by
-- proof
  apply StatMech.Lattice.dartOrbitWalk_length_pos K hK a

/--
[dartOrbitWalk_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartOrbitWalk_ne_nil_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  dartOrbitWalk K a ≠ SimpleGraph.Walk.nil := by
-- proof
  apply StatMech.Lattice.dartOrbitWalk_ne_nil K hK a

/--
[dartOrbitWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartOrbitWalk_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartOrbitWalk K a).support = (List.range (dartOrbitPeriod K a + 1)).map (fun k => (dartNextSub K)^[k] a) := by
-- proof
  apply StatMech.Lattice.dartOrbitWalk_support K a

/--
[iterate_inj_on_Icc_minimalPeriod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma iterate_inj_on_Icc_minimalPeriod_eq
  {f : α → α}
  {x : α}
  {j k : ℕ}
-- given
  (hpos : 0 < Function.minimalPeriod f x)
  (hj1 : 1 ≤ j)
  (hjp : j ≤ Function.minimalPeriod f x)
  (hk1 : 1 ≤ k)
  (hkp : k ≤ Function.minimalPeriod f x)
  (h : f^[j] x = f^[k] x) :
-- imply
  j = k := by
-- proof
  apply StatMech.Lattice.iterate_inj_on_Icc_minimalPeriod f x hpos hj1 hjp hk1 hkp h

/--
[dartOrbitWalk_support_tail_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean)
-/
@[path]
private lemma dartOrbitWalk_support_tail_nodup_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  (dartOrbitWalk K a).support.tail.Nodup := by
-- proof
  apply StatMech.Lattice.dartOrbitWalk_support_tail_nodup K hK a


-- created on 2026-10-23
