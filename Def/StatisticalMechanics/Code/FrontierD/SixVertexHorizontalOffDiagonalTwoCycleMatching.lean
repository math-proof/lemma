/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalOffDiagonalTwoCycleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalDiagonalDeficit.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalOffDiagonalTwoCycleSupport
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
        SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle -> Prop :=
  sixVertexHorizontalResidualConfigurationSupport T
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
    (fun _ source target =>
      SixVertexConfigurationPairTwoCycleFineRelated source.1 target.1)


def SixVertexHorizontalOffDiagonalTwoCycleMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  SixVertexHorizontalActualDeficitSupportedMatching T
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
    (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt)

end
end StatMech.FrontierD
