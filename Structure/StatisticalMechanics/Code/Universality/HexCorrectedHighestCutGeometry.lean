/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

structure HexCSCutData
    (W : ℕ) (hW : 0 < W) (source : List ℤ) where
  pre : List ℤ
  cutTurn : ℤ
  entryTurn : ℤ
  suffix : List ℤ
  finalTurn : ℤ
  source_eq :
    source = pre ++ [cutTurn] ++ suffix ++ [finalTurn]
  prefix_top :
    HexCSTopWalkAtWidth W hW
      (hexCSCutPrefixOutput pre cutTurn)
  suffix_top :
    HexCSTopWalkAtWidth W hW
      (hexCSCutSuffixOutput entryTurn suffix finalTurn)

end
end StatMech.Universality
