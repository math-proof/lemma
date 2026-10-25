/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRefinedTwoEast_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 + 2, p.2)
      [(p, 0), ((p.1 + 1, p.2), 0)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 0)
    (q := (p.1 + 1, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1 + 1, p.2), 0)
    (q := (p.1 + 2, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _

theorem fkRectRefinedTwoWest_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 - 2, p.2)
      [(p, 2), ((p.1 - 1, p.2), 2)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 2)
    (q := (p.1 - 1, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1 - 1, p.2), 2)
    (q := (p.1 - 2, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _

theorem fkRectRefinedTwoNorth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 + 2)
      [(p, 1), ((p.1, p.2 + 1), 1)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 1)
    (q := (p.1, p.2 + 1)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1, p.2 + 1), 1)
    (q := (p.1, p.2 + 2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _

theorem fkRectRefinedTwoSouth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 - 2)
      [(p, 3), ((p.1, p.2 - 1), 3)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 3)
    (q := (p.1, p.2 - 1)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1, p.2 - 1), 3)
    (q := (p.1, p.2 - 2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _


theorem fkRectRefinedLocalDarts_path
    (pairing : Bool) (c : Int × Int) (side : FKMedialSide) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c side)
      (fkRectRefinedDartPoint c
        (fkRectMedialLocalMateSide pairing side))
      (fkRectRefinedLocalDarts pairing c side) := by
  cases pairing <;> cases side
  · convert fkRectRefinedTwoEast_path
      (fkRectRefinedDartPoint c .west) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoWest_path
      (fkRectRefinedDartPoint c .east) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoEast_path
      (fkRectRefinedDartPoint c .south) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoWest_path
      (fkRectRefinedDartPoint c .north) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoNorth_path
      (fkRectRefinedDartPoint c .west) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoSouth_path
      (fkRectRefinedDartPoint c .east) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoSouth_path
      (fkRectRefinedDartPoint c .south) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoNorth_path
      (fkRectRefinedDartPoint c .north) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring


end
end StatMech.FrontierD
