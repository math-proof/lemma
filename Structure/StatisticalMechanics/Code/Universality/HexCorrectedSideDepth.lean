/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedSideDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds


namespace StatMech.Universality

open HexWalk

noncomputable section

structure HexCSNewSideDepthData (T : ℕ) (ts : List ℤ) where
  legal : (ofTurns hexAWStart 1 ts).IsLegalSAW
  physical_book_nonneg : ∀ k, k < ts.length →
    0 ≤ hexAWBookRe2 (hlhc_prefixCoord ts legal.1 k)
  depth_nonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts legal k
  terminal_depth_zero : hlhd_depth ts legal ts.length = 0
  terminal_white : (hlhc_prefixCoord ts legal.1 ts.length).color = .white
  cut_depth :
    hlhd_depth ts legal (hlhda_cutPos ts legal) = (T + 1 : ℤ)


end
end StatMech.Universality
