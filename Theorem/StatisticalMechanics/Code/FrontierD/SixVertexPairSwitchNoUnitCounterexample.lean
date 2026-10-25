/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample
open Finset


namespace StatMech.FrontierD

theorem sixVertexFourByTwoLowArrows_ice :
    sixVertexFourByTwoLowArrows.IceRule := by
  decide +revert

theorem sixVertexFourByTwoHighArrows_ice :
    sixVertexFourByTwoHighArrows.IceRule := by
  decide +revert

theorem sixVertexFourByTwoLowArrows_seamCount :
    sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus
      sixVertexFourByTwoLowArrows
      (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 := by
  decide +revert

theorem sixVertexFourByTwoHighArrows_seamCount :
    sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus
      sixVertexFourByTwoHighArrows
      (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 := by
  decide +revert


theorem sixVertexFourByTwo_localDisagreementDegree_two
    (v : sixVertexFourByTwoTorus.Vertex) :
    (∑ d, if sixVertexLocalIncomingPattern sixVertexFourByTwoLowArrows v d ≠
        sixVertexLocalIncomingPattern sixVertexFourByTwoHighArrows v d
      then 1 else 0) = 2 := by
  decide +revert


end StatMech.FrontierD
