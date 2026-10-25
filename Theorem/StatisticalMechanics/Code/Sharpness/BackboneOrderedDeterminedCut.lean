/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace shb_OrderedLocalTests

variable {E B : Type*} [DecidableEq E]


theorem accepted_mem_testedThrough (T : shb_OrderedLocalTests E B)
    (accepted : E) : accepted ∈ T.testedThrough accepted := by
  simp [testedThrough]


theorem exposure_subset_determinedCut (T : shb_OrderedLocalTests E B)
    (accepted e : E) (he : e ∈ T.testedThrough accepted) :
    T.exposure e ⊆ T.determinedCut accepted := by
  intro b hb
  exact ⟨e, he, hb⟩


theorem test_eq_of_mem_testedThrough
    (T : shb_OrderedLocalTests E B) (omega eta : B -> Bool)
    (accepted e : E)
    (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b)
    (he : e ∈ T.testedThrough accepted) :
    T.test omega e = T.test eta e := by
  apply T.test_local
  intro b hb
  exact hagree b (T.exposure_subset_determinedCut accepted e he hb)


theorem find?_eq_some_of_eq_on_testedThrough
    (test₁ test₂ : E -> Bool) (order : List E) (accepted : E)
    (hnodup : order.Nodup)
    (hfind : order.find? test₁ = some accepted)
    (hagree : ∀ e ∈ order.takeWhile (fun t => t != accepted) ++ [accepted],
      test₁ e = test₂ e) :
    order.find? test₂ = some accepted := by
  induction order with
  | nil => simp at hfind
  | cons a order ih =>
      rw [List.nodup_cons] at hnodup
      by_cases ha : a = accepted
      · subst a
        have htest₁ : test₁ accepted = true := List.find?_some hfind
        have hmem : accepted ∈
            (accepted :: order).takeWhile (fun t => t != accepted) ++ [accepted] := by
          simp
        have htest₂ : test₂ accepted = true := by
          rw [← hagree accepted hmem]
          exact htest₁
        simp [htest₂]
      · have htest₁ : test₁ a = false := by
          by_contra hne
          have htrue : test₁ a = true := Bool.eq_true_of_not_eq_false hne
          have hhead : (a :: order).find? test₁ = some a := by
            simp [htrue]
          have : some a = some accepted := hhead.symm.trans hfind
          exact ha (Option.some.inj this)
        have htailfind : order.find? test₁ = some accepted := by
          simpa [htest₁] using hfind
        have hprefix :
            (a :: order).takeWhile (fun t => t != accepted) ++ [accepted] =
              a :: (order.takeWhile (fun t => t != accepted) ++ [accepted]) := by
          simp [ha]
        have htest₂a : test₂ a = false := by
          have haMem : a ∈
              (a :: order).takeWhile (fun t => t != accepted) ++ [accepted] := by
            rw [hprefix]
            simp
          rw [← hagree a haMem]
          exact htest₁
        have htailagree : ∀ e ∈
            order.takeWhile (fun t => t != accepted) ++ [accepted],
            test₁ e = test₂ e := by
          intro e he
          apply hagree e
          rw [hprefix]
          simp [he]
        simpa [htest₂a] using ih hnodup.2 htailfind htailagree


theorem firstAccepted_eq_of_agreeOn_determinedCut
    (T : shb_OrderedLocalTests E B) (omega eta : B -> Bool)
    (accepted : E)
    (hfind : T.order.find? (T.test omega) = some accepted)
    (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b) :
    T.order.find? (T.test eta) = some accepted := by
  apply find?_eq_some_of_eq_on_testedThrough
    (T.test omega) (T.test eta) T.order accepted T.order_nodup hfind
  intro e he
  exact T.test_eq_of_mem_testedThrough omega eta accepted e hagree he


theorem firstAccepted_iff_of_agreeOn_determinedCut
    (T : shb_OrderedLocalTests E B) (omega eta : B -> Bool)
    (accepted : E)
    (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b) :
    T.order.find? (T.test omega) = some accepted <->
      T.order.find? (T.test eta) = some accepted := by
  constructor
  · exact fun h => T.firstAccepted_eq_of_agreeOn_determinedCut
      omega eta accepted h hagree
  · intro h
    apply T.firstAccepted_eq_of_agreeOn_determinedCut eta omega accepted h
    intro b hb
    exact (hagree b hb).symm

end shb_OrderedLocalTests
end
end StatMech.Sharpness
