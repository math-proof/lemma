import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitReachability
open SimpleGraph Equiv StatMech StatMech.FrontierD


/--
[fkMedial_boundary_sameCycle_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitReachability.lean)
-/
@[path]
private lemma fkMedial_boundary_sameCycle_of_walk_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialDart T}
  {p : (fkMedialLoopGraph T pairing).Walk d e}
-- given
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor e) :
-- imply
  (fkMedialBoundaryStep pairing).SameCycle d e := by
-- proof
  apply StatMech.FrontierD.fkMedial_boundary_sameCycle_of_walk pairing p hcolor

/--
[fkMedial_boundary_sameCycle_iff_reachable_of_color_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitReachability.lean)
-/
@[path]
private lemma fkMedial_boundary_sameCycle_iff_reachable_of_color_eq_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialDart T}
-- given
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor e) :
-- imply
  (fkMedialBoundaryStep pairing).SameCycle d e ↔ (fkMedialLoopGraph T pairing).Reachable d e := by
-- proof
  apply StatMech.FrontierD.fkMedial_boundary_sameCycle_iff_reachable_of_color_eq pairing d e hcolor

/--
[fkMedialCheckerColor_west_eq_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitReachability.lean)
-/
@[path]
private lemma fkMedialCheckerColor_west_eq_east_eq
  {T : EvenTorus}
  {v : T.Vertex} :
-- imply
  fkMedialCheckerColor (fkMedialWestDart v) = fkMedialCheckerColor (fkMedialEastDart v) := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerColor_west_eq_east v

/--
[fkMedial_west_east_sameCycle_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitReachability.lean)
-/
@[path]
private lemma fkMedial_west_east_sameCycle_iff_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  (fkMedialBoundaryStep pairing).SameCycle (fkMedialWestDart v) (fkMedialEastDart v) ↔ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v) := by
-- proof
  apply StatMech.FrontierD.fkMedial_west_east_sameCycle_iff_reachable pairing v

/--
[fkMedial_west_east_reachable_iff_exists_boundary_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitReachability.lean)
-/
@[path]
private lemma fkMedial_west_east_reachable_iff_exists_boundary_iterate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v) ↔ ∃ n : Nat, (fkMedialBoundaryStep pairing)^[n] (fkMedialWestDart v) = fkMedialEastDart v := by
-- proof
  apply StatMech.FrontierD.fkMedial_west_east_reachable_iff_exists_boundary_iterate pairing v


-- created on 2026-10-23
