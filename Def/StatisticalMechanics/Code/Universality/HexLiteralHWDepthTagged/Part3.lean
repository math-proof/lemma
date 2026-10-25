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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hlhdt_widthFiber
    (S : Finset HexHWContentHalf) (T : ℕ) : Finset HexBridge :=
  (hchb_bridges S).filter (fun b => b.width = T)

noncomputable def hlhdt_pickOrigin
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (b : {b // b ∈ hlhdt_widthFiber S T}) :
    HLHDBridgeOrigin b.1 :=
  Classical.choice (horigin b.1 (Finset.mem_filter.mp b.2).1)

noncomputable def hlhdt_fiberCode
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T)
    (b : {b // b ∈ hlhdt_widthFiber S T}) :
    HLHDColumnTag ×
      {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} :=
  hlhdt_originCode (hlhdt_pickOrigin S horigin T b) T hT
    (Finset.mem_filter.mp b.2).2

end
end StatMech.Universality
