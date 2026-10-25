/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualOpenBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoverageGeometry
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

def squareDualBoundaryShift : Site 2 := ![1, 1]


end
end StatMech.FrontierD
