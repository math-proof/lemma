/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Def.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

theorem boolSupport_injective {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (boolSupport : (I → Bool) → Finset I) := by
  intro a b h
  funext i
  have hi := Finset.ext_iff.mp h i
  simp [boolSupport] at hi
  cases hai : a i <;> cases hbi : b i <;> simp_all

theorem mem_boolAvoid_compl_support_iff {I : Type*}
    [Fintype I] [DecidableEq I] (a b : I → Bool) :
    a ∈ boolAvoid (Finset.univ \ boolSupport b) ↔
      boolSupport a ⊆ boolSupport b := by
  simp only [boolAvoid, Set.mem_setOf_eq]
  rw [Finset.disjoint_left]
  constructor
  · intro h x hxa
    by_contra hxb
    exact h hxa (by simp [hxb])
  · intro hsub x hxa hxb
    exact (Finset.mem_sdiff.mp hxb).2 (hsub hxa)

end StatMech.FrontierB
