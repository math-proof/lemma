/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexCorrectedSideDepth
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part8
import Abbrev.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hexCSCompletedSplit
    (T : ℕ) (hT : 1 ≤ T)
    (d : {ts : List ℤ // HexCSNewSideWalk T hT ts}) :
    HexCSCompletedTopWalk T hT × HexCSCompletedTopWalk T hT := by
  let G := hexCSNewSideDepthData T hT d
  let p := hlhda_completedPair d.1 G.legal
  refine ⟨⟨p.1, ?_⟩, ⟨p.2, ?_⟩⟩
  · have hp := hlhda_completedPrefix_mem_topAtWidth
      G.legal (T + 1) (by omega) G.depth_nonneg G.cut_depth
    simpa [p, hlhda_completedPair] using hp
  · have hs := hlhda_completedSuffix_mem_topAtWidth
      G.legal (T + 1) (by omega) G.depth_nonneg
      G.terminal_depth_zero G.terminal_white G.cut_depth
    simpa [p, hlhda_completedPair] using hs

end
end StatMech.Universality
