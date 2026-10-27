import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc4_dartnextperm.Part2
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc4_dartNextSub_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartNextSub_injective_eq
  {K : Set (Site 2)} :
-- imply
  Function.Injective (dartNextSub K) := by
-- proof
  apply StatMech.Walls.jc4_dartNextSub_injective K

/--
[jc4_dartNextSub_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartNextSub_bijective_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  Function.Bijective (dartNextSub K) := by
-- proof
  apply StatMech.Walls.jc4_dartNextSub_bijective K hK

/--
[jc4_dartNextSub_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartNextSub_surjective_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  Function.Surjective (dartNextSub K) := by
-- proof
  apply StatMech.Walls.jc4_dartNextSub_surjective K hK

/--
[jc4_dartNextSub_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartNextSub_ne_self_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  dartNextSub K a ≠ a := by
-- proof
  apply StatMech.Walls.jc4_dartNextSub_ne_self K a

/--
[jc4_dartNext_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartNext_periodic_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  ∃ p > 0, (dartNext K)^[p] e = e := by
-- proof
  apply StatMech.Walls.jc4_dartNext_periodic K hK e he

/--
[jc4_dartNextSub_mem_periodicPts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartNextSub_mem_periodicPts_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  a ∈ Function.periodicPts (dartNextSub K) := by
-- proof
  apply StatMech.Walls.jc4_dartNextSub_mem_periodicPts K hK a

/--
[jc4_dartOrbitPeriod_eq_minimalPeriod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartOrbitPeriod_eq_minimalPeriod_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := by
-- proof
  apply StatMech.Walls.jc4_dartOrbitPeriod_eq_minimalPeriod K a

/--
[jc4_dartOrbitPeriod_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartOrbitPeriod_pos_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  0 < dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc4_dartOrbitPeriod_pos K hK a

/--
[jc4_one_lt_dartOrbitPeriod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_one_lt_dartOrbitPeriod_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  1 < dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc4_one_lt_dartOrbitPeriod K hK a

/--
[jc4_dartOrbitPeriod_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartOrbitPeriod_iterate_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartNextSub K)^[dartOrbitPeriod K a] a = a := by
-- proof
  apply StatMech.Walls.jc4_dartOrbitPeriod_iterate K a

/--
[jc4_dartOrbitWalk_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartOrbitWalk_edges_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartOrbitWalk K a).edges = (List.range (dartOrbitPeriod K a)).map (fun k => s((dartNextSub K)^[k] a, (dartNextSub K)^[k + 1] a)) := by
-- proof
  apply StatMech.Walls.jc4_dartOrbitWalk_edges K a

/--
[jc4_dartOrbitWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartOrbitWalk_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  (dartOrbitWalk K a).IsCycle := by
-- proof
  apply StatMech.Walls.jc4_dartOrbitWalk_isCycle K hK a

/--
[jc4_dartNextPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean)
-/
@[path]
private lemma jc4_dartNextPerm_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  jc4_DartNextPerm K := by
-- proof
  apply StatMech.Walls.jc4_dartNextPerm K hK


-- created on 2026-10-23
