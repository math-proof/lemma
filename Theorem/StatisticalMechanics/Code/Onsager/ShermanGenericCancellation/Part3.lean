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
import Def.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation.Part3


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem rootedListTerm_glue (Lambda : Matrix E E ℂ) (e r : E)
    (ss : {ss : List (List E) // ons_validFactorList e r ss}) :
    ons_rootedListTerm Lambda e (ons_glue e ss.1) =
      ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss.1 := by
  have hfirst : ∀ s ∈ ss.1, ons_isFirstReturnSegment e s :=
    fun s hs => (ss.2 s hs).1
  have hhead : ∀ s ∈ ss.1, s.head? = some e :=
    fun s hs => ons_firstReturnSegment_head (hfirst s hs)
  have hlast : ∀ s ∈ ss.1, s.getLast? = some e :=
    fun s hs => ons_firstReturnSegment_last (hfirst s hs)
  unfold ons_rootedListTerm
  have hfactors : ons_firstReturnFactors e (ons_glue e ss.1) = ss.1 := by
    unfold ons_firstReturnFactors
    rw [ons_firstReturnSplit_glue e ss.1 hfirst]
    simp
  rw [hfactors, ons_edgeWeight_glue Lambda e ss.1 hhead hlast,
    listSeriesTerm_valid Lambda e r ss.1 ss.2]
  split_ifs with h
  · rw [h]
    simp
  · rfl


theorem ons_summable_rootedListTerm (Lambda : Matrix E E ℂ) (e r : E)
    (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    Summable fun w : {w : List E // ons_validRootedList e r w} =>
      ons_rootedListTerm Lambda e w.1 := by
  let eqv := ons_rootedFactorEquiv e r her
  have hall := ons_summable_listSeriesTerm
    (ons_firstReturnWeight Lambda e r) hsum hsmall
  have hfactor := hall.subtype (ons_validFactorList e r)
  have heqv : Summable fun w : {w : List E // ons_validRootedList e r w} =>
      ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) (eqv w).1 := by
    simpa only [Function.comp_apply] using (eqv.summable_iff.mpr hfactor)
  apply heqv.congr
  intro w
  have hinv := congrArg Subtype.val (eqv.left_inv w)
  change ons_glue e (eqv w).1 = w.1 at hinv
  rw [← hinv]
  exact (rootedListTerm_glue Lambda e r (eqv w)).symm


theorem ons_rootedListSeries_eq_geometric (Lambda : Matrix E E ℂ) (e r : E)
    (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    (∑' w : {w : List E // ons_validRootedList e r w}, ons_rootedListTerm Lambda e w.1) =
      ∑' k : ℕ, (∑' s, ons_firstReturnWeight Lambda e r s) ^ (k + 1) / (k + 1) := by
  let eqv := ons_rootedFactorEquiv e r her
  calc
    (∑' w : {w : List E // ons_validRootedList e r w}, ons_rootedListTerm Lambda e w.1) =
        ∑' ss : {ss : List (List E) // ons_validFactorList e r ss},
          ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss.1 := by
            rw [← eqv.tsum_eq]
            apply tsum_congr
            intro w
            have hinv := congrArg Subtype.val (eqv.left_inv w)
            change ons_glue e (eqv w).1 = w.1 at hinv
            change ons_rootedListTerm Lambda e w.1 =
              ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) (eqv w).1
            rw [← hinv]
            exact rootedListTerm_glue Lambda e r (eqv w)
    _ = ∑' ss : List (List E),
          ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss := by
            have hsub := tsum_subtype
              {ss : List (List E) | ons_validFactorList e r ss}
              (ons_listSeriesTerm (ons_firstReturnWeight Lambda e r))
            change (∑' ss : {ss : List (List E) // ons_validFactorList e r ss},
                ons_listSeriesTerm
              (ons_firstReturnWeight Lambda e r) ss.1) = _ at hsub
            rw [hsub]
            apply tsum_congr
            intro ss
            by_cases hvalid : ons_validFactorList e r ss
            · simp [Set.indicator, hvalid]
            · simp [Set.indicator, hvalid,
                listSeriesTerm_eq_zero_of_invalid Lambda e r ss hvalid]
    _ = _ := ons_tsum_listSeriesTerm _ hsum hsmall

end StatMech.Onsager
