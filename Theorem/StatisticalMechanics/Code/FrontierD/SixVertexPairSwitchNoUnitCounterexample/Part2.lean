/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
open Finset


namespace StatMech.FrontierD

theorem sixVertexFourByTwo_switchFirst_eq_reduced
    (mask : SixVertexArrows sixVertexFourByTwoTorus) :
    sixVertexTorusSwitchFirst mask
        sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows =
      sixVertexFourByTwoReducedArrows
        (sixVertexFourByTwoReducedMaskOf mask) := by
  apply SixVertexArrows.ext
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;>
      simp [sixVertexTorusSwitchFirst, sixVertexFourByTwoLowArrows,
        sixVertexFourByTwoHighArrows, sixVertexFourByTwoReducedMaskOf,
        sixVertexFourByTwoReducedArrows, sixVertexFourByTwoVertex]
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;>
      simp [sixVertexTorusSwitchFirst, sixVertexFourByTwoLowArrows,
        sixVertexFourByTwoHighArrows, sixVertexFourByTwoReducedMaskOf,
        sixVertexFourByTwoReducedArrows, sixVertexFourByTwoVertex]

set_option maxRecDepth 10000 in
theorem sixVertexFourByTwo_reduced_no_ice_to_middle
    (r : SixVertexFourByTwoReducedMask) :
    ¬ ((sixVertexFourByTwoReducedArrows r).IceRule /\
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByTwoTorus
          (sixVertexFourByTwoReducedArrows r)
          (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
  decide +revert


theorem sixVertexFourByTwo_no_icePairSwitch_to_middle
    (mask : SixVertexArrows sixVertexFourByTwoTorus) :
    ¬ ((sixVertexTorusSwitchFirst mask
          sixVertexFourByTwoLowArrows
          sixVertexFourByTwoHighArrows).IceRule /\
      (sixVertexTorusSwitchSecond mask
          sixVertexFourByTwoLowArrows
          sixVertexFourByTwoHighArrows).IceRule /\
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByTwoTorus
          (sixVertexTorusSwitchFirst mask
            sixVertexFourByTwoLowArrows
            sixVertexFourByTwoHighArrows)
          (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
  intro hbad
  have hfirst := sixVertexFourByTwo_reduced_no_ice_to_middle
    (sixVertexFourByTwoReducedMaskOf mask)
  apply hfirst
  rw [← sixVertexFourByTwo_switchFirst_eq_reduced]
  exact ⟨hbad.1, hbad.2.2⟩

end StatMech.FrontierD
