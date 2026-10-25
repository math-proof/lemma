/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry


namespace StatMech.Universality

open HexWalk

noncomputable section

def hexCSCutPrefixOutput
    (pre : List ℤ) (cutTurn : ℤ) : List ℤ :=
  pre ++ [-cutTurn]


def hexCSCutSuffixOutput
    (entryTurn : ℤ) (suffix : List ℤ) (finalTurn : ℤ) : List ℤ :=
  (entryTurn :: suffix) ++ [finalTurn]


def hexCSDecodeCutPair (out : List ℤ × List ℤ) : List ℤ :=
  out.1.dropLast ++ [-out.1.getLastD 0] ++
    out.2.dropLast.tail ++ [out.2.getLastD 0]

end
end StatMech.Universality
