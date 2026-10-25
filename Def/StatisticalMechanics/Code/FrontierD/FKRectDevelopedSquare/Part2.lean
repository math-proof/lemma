/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedSquareVertex (R : FKRectTorus) (n : Nat)
    (z : Site 2) : R.Vertex :=
  fkRectSquareRepresentativeVertex R (fkRectDevelopedSquarePoint n z)

end
end StatMech.FrontierD
