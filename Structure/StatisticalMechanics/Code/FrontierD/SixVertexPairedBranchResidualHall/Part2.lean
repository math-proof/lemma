/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall
open Finset


namespace StatMech.FrontierD

noncomputable section

structure SixVertexHorizontalPairedBranchResidualGeometricConstruction
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  targetConfiguration :
    SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
      Bool ->
        {pair : SixVertexMarkedSectorConfiguration T middle ×
            SixVertexMarkedSectorConfiguration T middle //
          sixVertexConfigurationPairBigrade pair = grade}
  realization : forall source branch,
    SixVertexHorizontalSurplusConfigurationPreimage T middle
      hmiddle_pos hmiddle_lt grade (targetConfiguration source branch)
  distinct : forall source,
    targetConfiguration source false ≠ targetConfiguration source true
  recoverable : forall branch first second,
    targetConfiguration first branch = targetConfiguration second branch ->
      sixVertexHorizontalActualDeficitConfigurationPair first =
        sixVertexHorizontalActualDeficitConfigurationPair second
  supported : forall source branch,
    SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source).1
      (targetConfiguration source branch).1


end
end StatMech.FrontierD
