/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedTopWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedTopWitness


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hexCSTopOneData :
    HLHCCanonicalColumnWalk 1 [1, -1] where
  legal := hexCSTopOne_legal
  horizontal := by
    intro k hk
    norm_num at hk
    interval_cases k
    · rw [hexCSTopOne_prefix_zero]
      norm_num [hexAWBookRe2, hexAWDepth, hexAWLong,
        hexAWOriginCoord]
    · rw [hexCSTopOne_prefix_one]
      norm_num [hexAWBookRe2, hexAWDepth, hexAWLong]
  topCoord := ⟨0, -1, .white⟩
  top_white := rfl
  top_depth := by
    norm_num [hexAWDepth, hexAWLong]
  endsAt := by
    rw [HexWalk.EndsAt, hexInfra_endMid_eq_midAccum]
    simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil]
    unfold hexAWMid hexAWPos hexAWNeighbor hexAWBasisJ hexAWAxis
      hexAWStart halfStep
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring


end
end StatMech.Universality
