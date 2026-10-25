/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part6


namespace StatMech.Universality

open List


def hexHW_IsValidWalk (γ : List (ℕ × ℤ)) : Prop :=
  ∃ bs, StrictDecreasingWidths bs ∧ bridgeRecompose bs = γ


noncomputable def hexHW_bridge_decomp :
    {bs : List HexBridge // StrictDecreasingWidths bs} ≃
      {γ : List (ℕ × ℤ) // hexHW_IsValidWalk γ} :=
  Equiv.ofBijective
    (fun bs => ⟨bridgeRecompose bs.1, bs.1, bs.2, rfl⟩)
    (by
      constructor
      · 
        intro bs cs heq
        apply Subtype.ext
        have : bridgeRecompose bs.1 = bridgeRecompose cs.1 := congrArg Subtype.val heq
        exact hexHW_bridgeRecompose_injOn bs.2 cs.2 this
      · 
        intro γ
        obtain ⟨bs, hbs, hrec⟩ := γ.2
        exact ⟨⟨bs, hbs⟩, by apply Subtype.ext; exact hrec⟩)


end StatMech.Universality
