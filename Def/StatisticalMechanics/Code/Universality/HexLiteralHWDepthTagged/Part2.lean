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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hlhdt_originCode {b : HexBridge}
    (o : HLHDBridgeOrigin b) (T : ℕ) (hT : 0 < T)
    (hbT : b.width = T) :
    HLHDColumnTag ×
      {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} :=
  let hwidth : hlhd_width o.turns o.legal o.interval = T :=
    o.width_eq.symm.trans hbT
  (hlhd_intervalTag o.turns o.legal o.halfSpace
      o.interval o.interval_mem,
    ⟨hlhd_intervalEndpoint o.turns o.legal o.halfSpace
        o.interval o.interval_mem,
      by
        have hmem := hlhd_intervalEndpoint_mem_topAtWidth
          o.turns o.legal o.halfSpace o.interval o.interval_mem
        simpa only [hwidth] using hmem⟩)

end
end StatMech.Universality
