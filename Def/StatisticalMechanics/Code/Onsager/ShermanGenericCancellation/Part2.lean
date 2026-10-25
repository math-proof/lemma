/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanListSeries.Part2
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot.Part4
import Theorem.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

def ons_rootedFactorEquiv (e r : E) (her : e ≠ r) :
    {w : List E // ons_validRootedList e r w} ≃
      {ss : List (List E) // ons_validFactorList e r ss} where
  toFun w := ⟨ons_firstReturnFactors e w.1,
    firstReturnFactors_valid e r w.1 w.2⟩
  invFun ss := ⟨ons_glue e ss.1, by
    have hfirst : ∀ s ∈ ss.1, ons_isFirstReturnSegment e s :=
      fun s hs => (ss.2 s hs).1
    have hhead : ∀ s ∈ ss.1, s.head? = some e :=
      fun s hs => ons_firstReturnSegment_head (hfirst s hs)
    have hlast : ∀ s ∈ ss.1, s.getLast? = some e :=
      fun s hs => ons_firstReturnSegment_last (hfirst s hs)
    refine ⟨?_, ?_, avoids_glue e r her ss.1 ss.2⟩
    · obtain ⟨tail, htail⟩ := ons_glue_head e ss.1 hhead
      rw [htail]
      simp
    · exact glue_getLast e ss.1⟩
  left_inv w := by
    apply Subtype.ext
    exact (ons_firstReturnFactors_spec e w.1 w.2.1 w.2.2.1).2.2
  right_inv ss := by
    apply Subtype.ext
    have hfirst : ∀ s ∈ ss.1, ons_isFirstReturnSegment e s :=
      fun s hs => (ss.2 s hs).1
    change ons_firstReturnFactors e (ons_glue e ss.1) = ss.1
    unfold ons_firstReturnFactors
    rw [ons_firstReturnSplit_glue e ss.1 hfirst]
    simp

noncomputable def ons_firstReturnWeight (Lambda : Matrix E E ℂ) (e r : E)
    (s : List E) : ℂ := by
  classical
  exact if ons_isFirstReturnSegment e s ∧ (∀ x ∈ s, x ≠ r) then
      ons_edgeWeight Lambda s
    else 0

end StatMech.Onsager
