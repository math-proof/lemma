import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[permOrbitVisitCount_eq_of_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean)
-/
@[path]
private lemma permOrbitVisitCount_eq_of_sameCycle_eq
  {T : EvenTorus}
  [Fintype α]
  [DecidableEq α]
  {σ : Perm α}
  {d a b : α}
-- given
  (hab : σ.SameCycle a b) :
-- imply
  permOrbitVisitCount σ d a = permOrbitVisitCount σ d b := by
-- proof
  apply StatMech.FrontierD.permOrbitVisitCount_eq_of_sameCycle σ d a b hab

/--
[permOrbitVisitCount_pos_iff_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean)
-/
@[path]
private lemma permOrbitVisitCount_pos_iff_sameCycle_eq
  {T : EvenTorus}
  [Fintype α]
  [DecidableEq α]
  {σ : Perm α}
  {d e : α} :
-- imply
  0 < permOrbitVisitCount σ d e ↔ σ.SameCycle d e := by
-- proof
  apply StatMech.FrontierD.permOrbitVisitCount_pos_iff_sameCycle σ d e

/--
[permOrbitVisitCount_eq_zero_iff_not_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean)
-/
@[path]
private lemma permOrbitVisitCount_eq_zero_iff_not_sameCycle_eq
  {T : EvenTorus}
  [Fintype α]
  [DecidableEq α]
  {σ : Perm α}
  {d e : α} :
-- imply
  permOrbitVisitCount σ d e = 0 ↔ ¬ σ.SameCycle d e := by
-- proof
  apply StatMech.FrontierD.permOrbitVisitCount_eq_zero_iff_not_sameCycle σ d e

/--
[fkMedial_west_east_visitCount_eq_zero_iff_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean)
-/
@[path]
private lemma fkMedial_west_east_visitCount_eq_zero_iff_not_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialBoundaryOrbitVisitCount pairing (fkMedialWestDart v) (fkMedialEastDart v) = 0 ↔ ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v) := by
-- proof
  apply StatMech.FrontierD.fkMedial_west_east_visitCount_eq_zero_iff_not_reachable pairing v

/--
[fkMedial_west_visitCount_eq_east_visitCount_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean)
-/
@[path]
private lemma fkMedial_west_visitCount_eq_east_visitCount_iff_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialBoundaryOrbitVisitCount pairing (fkMedialWestDart v) (fkMedialWestDart v) = fkMedialBoundaryOrbitVisitCount pairing (fkMedialWestDart v) (fkMedialEastDart v) ↔ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v) := by
-- proof
  apply StatMech.FrontierD.fkMedial_west_visitCount_eq_east_visitCount_iff_reachable pairing v

/--
[fkMedial_west_sub_east_visitCount_ne_zero_iff_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean)
-/
@[path]
private lemma fkMedial_west_sub_east_visitCount_ne_zero_iff_not_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  ((fkMedialBoundaryOrbitVisitCount pairing (fkMedialWestDart v) (fkMedialWestDart v) : Int) - fkMedialBoundaryOrbitVisitCount pairing (fkMedialWestDart v) (fkMedialEastDart v) ≠ 0) ↔ ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v) := by
-- proof
  apply StatMech.FrontierD.fkMedial_west_sub_east_visitCount_ne_zero_iff_not_reachable pairing v


-- created on 2026-10-23
