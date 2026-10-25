/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalSurplusConfigurationPreimage
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat)
    (configuration : {pair : SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle //
      sixVertexConfigurationPairBigrade pair = grade}) :=
  {token : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualSurplusConfigurationPair token = configuration}


end
end StatMech.FrontierD
