/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Structure.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry


namespace StatMech.Universality

open HexWalk

noncomputable section

namespace HexCSCutData

variable {W : ℕ} {hW : 0 < W} {source : List ℤ}

def outputPair (D : HexCSCutData W hW source) : List ℤ × List ℤ :=
  (hexCSCutPrefixOutput D.pre D.cutTurn,
    hexCSCutSuffixOutput D.entryTurn D.suffix D.finalTurn)

end HexCSCutData
end
end StatMech.Universality
