/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWColumns


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhr_stripColumnRealization_zero_column (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (p : ℕ × ℕ) (hp : p ∈ hlhr_literalIntervals 0 ts) :
    (hlhr_stripColumnRealization_zero ts hleg hhalf).column p hp =
      hlhr_latticeWidth ts p := rfl


theorem hlhr_literalBridge_mem_with_column (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (b : HexBridge) (hb : b ∈ hlhr_literalBridgeList ts hleg hhalf) :
    ∃ p : {p // p ∈ hlhr_literalIntervals 0 ts},
      b = hlhr_literalBridge ts hleg hhalf p ∧
        b.width = (hlhr_stripColumnRealization_zero ts hleg hhalf).column p.1 p.2 := by
  unfold hlhr_literalBridgeList at hb
  rw [List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  exact ⟨p, rfl, rfl⟩


end
end StatMech.Universality
