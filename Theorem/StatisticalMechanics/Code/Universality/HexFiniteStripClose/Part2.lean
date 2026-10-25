/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


theorem hfs_legality_fires :
    (ofTurns (0 : ℂ) 0 [1, -1]).LegalTurns ∧
    (ofTurns (0 : ℂ) 0 ([1, -1].take 1)).LegalTurns ∧
    (ofTurns (0 : ℂ) 0 [1, -1]).numVertices = 3 ∧
    (ofTurns (0 : ℂ) 0 ([1, -1].take 1)).numVertices = 2 ∧
    (ofTurns (0 : ℂ) 0 ([1, -1].drop 1)).numVertices = 2 := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro t ht; simp only [ofTurns_turns, List.mem_cons] at ht
    rcases ht with h | h | h <;> simp_all
  · intro t ht; simp only [ofTurns_turns, List.take, List.mem_cons] at ht
    rcases ht with h | h <;> simp_all

end StatMech.Universality
