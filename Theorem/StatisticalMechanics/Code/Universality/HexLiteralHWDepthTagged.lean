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
import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hlhdt_bridge_eq_of_width_content {b c : HexBridge}
    (hwidth : b.width = c.width) (hcontent : b.content = c.content) :
    b = c := by
  rcases b with ⟨bw, hbpos, bc, hbc⟩
  rcases c with ⟨cw, hcpos, cc, hcc⟩
  simp only at hwidth hcontent
  subst cw
  subst cc
  rfl

theorem HLHDBridgeOrigin.width_eq {b : HexBridge}
    (o : HLHDBridgeOrigin b) :
    b.width = hlhd_width o.turns o.legal o.interval := by
  have h := congrArg HexBridge.width o.bridge_eq
  simpa [hlhd_bridge] using h

theorem HLHDBridgeOrigin.content_eq {b : HexBridge}
    (o : HLHDBridgeOrigin b) :
    b.content = hlhd_intervalRaw o.turns o.interval := by
  have h := congrArg HexBridge.content o.bridge_eq
  simpa [hlhd_bridge, hlhd_intervalRaw] using h

theorem hlhdt_contentHalf_bridge_origin (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    {b : HexBridge} (hb : b ∈ (hlhd_contentHalf ts hleg hhalf).1) :
    Nonempty (HLHDBridgeOrigin b) := by
  change b ∈ hlhd_bridgeList ts hleg hhalf at hb
  unfold hlhd_bridgeList at hb
  rw [List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  exact ⟨{
    turns := ts
    legal := hleg
    halfSpace := hhalf
    interval := p.1
    interval_mem := p.2
    bridge_eq := rfl
  }⟩

end
end StatMech.Universality
