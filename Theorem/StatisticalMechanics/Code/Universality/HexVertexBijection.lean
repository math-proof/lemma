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
import Abbrev.StatisticalMechanics.Code.Universality.HexVertexBijection


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hinj_of_leftInverse (E : HexVertexEnumeration region a h0 v du)
    (cls : List ℤ → SlotType E)
    (hleft : ∀ slot ∈ Function.support (combinedSummand region a h0 v du ∘ E.slotTurns),
        cls (E.slotTurns slot) = slot) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only at h
  apply Subtype.ext
  have hc : cls (E.slotTurns x) = cls (E.slotTurns y) := by rw [h]
  rw [hleft x hx, hleft y hy] at hc
  exact hc


theorem hsub_of_rightInverse (E : HexVertexEnumeration region a h0 v du)
    (cls : List ℤ → SlotType E)
    (hright : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        E.slotTurns (cls ts) = ts) :
    Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  intro ts hts
  have hst : E.slotTurns (cls ts) = ts := hright ts hts
  have hmem : cls ts ∈ Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) := by
    simp only [Function.mem_support, Function.comp_apply, hst]
    exact hts
  exact ⟨⟨cls ts, hmem⟩, hst⟩


end StatMech.Universality
