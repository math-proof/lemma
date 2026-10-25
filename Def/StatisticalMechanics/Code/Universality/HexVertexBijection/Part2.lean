/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def HexVertexBijection.ofInjectiveRightInverse
    (E : HexVertexEnumeration region a h0 v du)
    (classify : List ℤ → SlotType E)
    (hsti : Function.Injective E.slotTurns)
    (hright : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        E.slotTurns (classify ts) = ts) :
    HexVertexBijection region a h0 v du where
  enum := E
  classify := classify
  classify_slotTurns := by
    intro slot hslot
    have hf : E.slotTurns slot ∈ Function.support (combinedSummand region a h0 v du) := by
      rw [Function.mem_support] at hslot ⊢
      exact hslot
    exact hsti (hright (E.slotTurns slot) hf)
  slotTurns_classify := hright


end StatMech.Universality
