/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding.Part2
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar

noncomputable section

def squareOffsetVertex (offset : Complex) : Site 2 ↪ Complex where
  toFun x := squareComplexPoint x + offset
  inj' := fun _ _ h => squareComplexPoint_injective (add_right_cancel h)

end
end StatMech.FrontierD
