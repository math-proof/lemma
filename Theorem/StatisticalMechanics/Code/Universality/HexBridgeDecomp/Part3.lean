/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part3


namespace StatMech.Universality

open List


@[simp]
theorem bridgeRecompose_nil : bridgeRecompose [] = [] := rfl

@[simp]
theorem bridgeRecompose_cons (b : HexBridge) (bs : List HexBridge) :
    bridgeRecompose (b :: bs) = b.rungs ++ bridgeRecompose bs := by
  simp [bridgeRecompose]

theorem bridgeRecompose_append (bs cs : List HexBridge) :
    bridgeRecompose (bs ++ cs) = bridgeRecompose bs ++ bridgeRecompose cs := by
  simp [bridgeRecompose, List.flatten_append]


theorem mem_bridgeRecompose_fst {bs : List HexBridge} {p : ℕ × ℤ}
    (hp : p ∈ bridgeRecompose bs) : ∃ b ∈ bs, p.1 = b.width := by
  induction bs with
  | nil => simp [bridgeRecompose] at hp
  | cons b bs ih =>
    rw [bridgeRecompose_cons, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨b, List.mem_cons_self, HexBridge.mem_rungs_fst hp⟩
    · obtain ⟨c, hc, hpc⟩ := ih hp
      exact ⟨c, List.mem_cons_of_mem b hc, hpc⟩


end StatMech.Universality
