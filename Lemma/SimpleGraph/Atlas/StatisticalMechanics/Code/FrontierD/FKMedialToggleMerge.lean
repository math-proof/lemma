import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
open Equiv SimpleGraph StatMech StatMech.FrontierD


/--
[fkMedialLoopGraph_toggle_reachable_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean)
-/
@[path]
private lemma fkMedialLoopGraph_toggle_reachable_of_not_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
-- given
  (hold : ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v)) :
-- imply
  (fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v)).Reachable (fkMedialWestDart v) (fkMedialEastDart v) := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_toggle_reachable_of_not_reachable pairing v hold

/--
[fkMedialBlackBoundaryPerm_toggle_merge_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_toggle_merge_partition_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  {x : FKMedialBlackDart T}
-- given
  (hold : ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v)) :
-- imply
  (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)).SameCycle (fkMedialBlackDart0 v) x ↔ (fkMedialBlackBoundaryPerm pairing).SameCycle (fkMedialBlackDart0 v) x ∨ (fkMedialBlackBoundaryPerm pairing).SameCycle (fkMedialBlackDart1 v) x := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_toggle_merge_partition pairing v hold x

/--
[fkMedialBlackBoundaryPerm_toggle_sameCycle_iff_of_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_toggle_sameCycle_iff_of_away_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  {x y : FKMedialBlackDart T}
-- given
  (hold : ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v))
  (hx : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle (fkMedialBlackDart0 v) x)
  (hx' : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle (fkMedialBlackDart1 v) x) :
-- imply
  (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)).SameCycle x y ↔ (fkMedialBlackBoundaryPerm pairing).SameCycle x y := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_toggle_sameCycle_iff_of_away pairing v hold hx hx'

/--
[fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  {x y : FKMedialBlackDart T}
-- given
  (hold : ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v))
  (hxy : (fkMedialBlackBoundaryPerm pairing).SameCycle x y) :
-- imply
  (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)).SameCycle x y := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable pairing v hold hxy

/--
[fkMedial_reachable_blackRepresentative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean)
-/
@[path]
private lemma fkMedial_reachable_blackRepresentative_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLoopGraph T pairing).Reachable d (fkMedialBlackRepresentative T d).1 := by
-- proof
  apply StatMech.FrontierD.fkMedial_reachable_blackRepresentative pairing d

/--
[fkMedialLoopGraph_toggle_reachable_mono_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean)
-/
@[path]
private lemma fkMedialLoopGraph_toggle_reachable_mono_of_not_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  {d e : FKMedialDart T}
-- given
  (hold : ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v))
  (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
-- imply
  (fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v)).Reachable d e := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_toggle_reachable_mono_of_not_reachable pairing v hold hde


-- created on 2026-10-23
