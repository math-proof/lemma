/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionSurfaceAssembly
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedConnectedInsertionCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectInsertedEdgeStepCharge (R : FKRectTorus) (e : R.EdgeIndex)
    (x y : R.Vertex) : Int :=
  if x = fkRectMedialWestPrimal R e ∧
      y = fkRectMedialEastPrimal R e then -1
  else if x = fkRectMedialEastPrimal R e ∧
      y = fkRectMedialWestPrimal R e then 1
  else 0


def fkRectInsertedEdgeCharge (R : FKRectTorus) (e : R.EdgeIndex)
    {G : SimpleGraph R.Vertex} {x y : R.Vertex} : G.Walk x y → Int
  | .nil' _ => 0
  | .cons' x z _ _ p =>
      fkRectInsertedEdgeStepCharge R e x z +
        fkRectInsertedEdgeCharge R e p

end
end StatMech.FrontierD
