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
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedSquarePoint (n : Nat) (z : Site 2) : Int × Int :=
  (z 0 + 2 * n, z 1 + n)

def fkRectDevelopedSquareSite (n : Nat) (z : Site 2) : Site 2 :=
  fkRectSquareSiteOfPair (fkRectDevelopedSquarePoint n z)


def fkRectSquareSiteVertex (R : FKRectTorus) (z : Site 2) : R.Vertex :=
  fkRectSquareRepresentativeVertex R (z 0, z 1)

end
end StatMech.FrontierD
