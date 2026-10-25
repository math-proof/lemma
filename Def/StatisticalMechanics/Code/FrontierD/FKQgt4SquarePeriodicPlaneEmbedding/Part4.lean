/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding.Part3
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar

noncomputable section

def squareOffsetEdgeArc (offset : Complex) {x y : Site 2}
    (_hxy : square.graph.Adj x y) :
    Path (squareOffsetVertex offset x) (squareOffsetVertex offset y) :=
  Path.segment _ _

end
end StatMech.FrontierD
