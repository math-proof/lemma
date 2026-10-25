/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part7
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectOpenGraphQuarterTurnIso
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) where
  toEquiv := fkRectQuarterTurnVertexEquiv R hheight
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_quarterTurn_adj R hheight omega x y


end
end StatMech.FrontierD
