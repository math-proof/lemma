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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hlhdt_contentHalfImage_origin
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    (b : HexBridge)
    (hb : b ∈ hchb_bridges
      (hlhdt_contentHalfImage D turns legal halfSpace)) :
    Nonempty (HLHDBridgeOrigin b) := by
  classical
  unfold hchb_bridges at hb
  rw [Finset.mem_biUnion] at hb
  obtain ⟨s, hs, hbs⟩ := hb
  unfold hlhdt_contentHalfImage at hs
  rw [Finset.mem_image] at hs
  obtain ⟨d, _, rfl⟩ := hs
  exact hlhdt_contentHalf_bridge_origin (turns d) (legal d)
    (halfSpace d) (List.mem_toFinset.mp hbs)


end
end StatMech.Universality
