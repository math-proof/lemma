/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Def.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem noCrossingK_of_event (ends : ι → Sym2 V) (m : Finset ι) (S : Finset V) (o : V)
    (_ho : o ∉ S) (hev : notConnCompK ends m o = S) : NoCrossingK ends m S := by
  intro i hi
  obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · left; intro w hw; rw [← hab, Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
  · 
    exfalso
    by_cases hab' : a = b
    · subst hab'; exact hb ha
    · have hadj : adjStep ends m a b :=
        ⟨i, hi, hab ▸ Sym2.mem_mk_left a b, hab ▸ Sym2.mem_mk_right a b, hab'⟩
      have hbo : connK ends m o b := by
        by_contra hc; exact hb (hev ▸ (mem_notConnCompK).mpr hc)
      have hao : connK ends m o a :=
        Relation.ReflTransGen.tail hbo (adjStep_symm ends m hadj)
      exact ((mem_notConnCompK (o := o) (w := a)).not.mpr (not_not.mpr hao)) (hev ▸ ha)
  · 
    exfalso
    by_cases hab' : a = b
    · subst hab'; exact ha hb
    · have hadj : adjStep ends m a b :=
        ⟨i, hi, hab ▸ Sym2.mem_mk_left a b, hab ▸ Sym2.mem_mk_right a b, hab'⟩
      have hao : connK ends m o a := by
        by_contra hc; exact ha (hev ▸ (mem_notConnCompK).mpr hc)
      have hbo : connK ends m o b := Relation.ReflTransGen.tail hao hadj
      exact ((mem_notConnCompK (o := o) (w := b)).not.mpr (not_not.mpr hbo)) (hev ▸ hb)
  · right; intro w hw; rw [Finset.mem_compl]; rw [← hab, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption


end RandomCurrent
end Sharpness
end StatMech
