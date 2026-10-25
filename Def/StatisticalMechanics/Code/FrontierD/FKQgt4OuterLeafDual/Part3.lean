/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Instance.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

def pfdOuterLeafCollapse (P : PlanarZ2Subgraph) :
    pfdOuterLeafVertex P → kwg_Face P
  | Sum.inl C => C.1
  | Sum.inr _ => pfdOuterFace P


def pfdOuterLeafSideFace (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (side : Bool) : kwg_Face P :=
  if side then
    (whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankRight P e)
  else
    (whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankLeft P e)


def pfdOuterLeafEndpoint (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (side : Bool) : pfdOuterLeafVertex P :=
  if h : pfdOuterLeafSideFace P e side = pfdOuterFace P then
    Sum.inr (Sum.inr (e, side))
  else
    Sum.inl ⟨pfdOuterLeafSideFace P e side, h⟩

end
end StatMech.FrontierD
