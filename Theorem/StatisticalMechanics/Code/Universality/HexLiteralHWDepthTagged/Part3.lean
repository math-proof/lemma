/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hlhdt_originCode_decode {b : HexBridge}
    (o : HLHDBridgeOrigin b) (T : ℕ) (hT : 0 < T)
    (hbT : b.width = T) :
    hlhd_decodeColumn (hlhdt_originCode o T hT hbT).1
        (hlhdt_originCode o T hT hbT).2.1 = b.content := by
  rw [hlhdt_originCode]
  exact (hlhd_interval_decode o.turns o.legal o.halfSpace
    o.interval o.interval_mem).trans o.content_eq.symm

end
end StatMech.Universality
