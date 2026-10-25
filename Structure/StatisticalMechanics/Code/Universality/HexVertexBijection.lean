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
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


structure HexVertexBijection (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  

  enum : HexVertexEnumeration region a h0 v du
  
  classify : List ℤ → SlotType enum
  


  classify_slotTurns : ∀ slot ∈ Function.support
      (combinedSummand region a h0 v du ∘ enum.slotTurns),
    classify (enum.slotTurns slot) = slot
  

  slotTurns_classify : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    enum.slotTurns (classify ts) = ts

end StatMech.Universality
