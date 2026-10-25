/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Def.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

namespace HexCSCutData

variable {W : ℕ} {hW : 0 < W} {source : List ℤ}

@[simp] theorem decode_outputPair (D : HexCSCutData W hW source) :
    hexCSDecodeCutPair D.outputPair = source := by
  rw [outputPair, hexCSDecodeCutPair_encode, ← D.source_eq]

@[simp] theorem output_length_add_one (D : HexCSCutData W hW source) :
    D.outputPair.1.length + D.outputPair.2.length = source.length + 1 := by
  rw [outputPair, hexCSCutPair_length_add_one, ← D.source_eq]

end HexCSCutData
end
end StatMech.Universality
