/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part9
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem cycleTranslation_pairBalance_nonneg_of_coversNegative
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (z : sourceMaskCycleSpace ends p)
    (hcovers : CycleTranslationCoversNegative ends m j k l zero p z)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    0 ≤ reversalGateBalance ends m j k l zero p c +
      reversalGateBalance ends m j k l zero p
        (sourceMaskCycleAction ends m j k l zero p c z) := by
  let d := sourceMaskCycleAction ends m j k l zero p c z
  have hdc : sourceMaskCycleAction ends m j k l zero p d z = c :=
    sourceMaskCycleAction_involutive ends m j k l zero p z c
  change 0 ≤ reversalGateBalance ends m j k l zero p c +
    reversalGateBalance ends m j k l zero p d
  have nonneg_of_not_negative : ∀ q :
      leftSourceMaskFiber ends m j k l zero p,
      ¬ ReversalGateNegative ends m j k l zero p q ->
        0 ≤ reversalGateBalance ends m j k l zero p q := by
    intro q hq
    classical
    by_cases hL : RowsDisconnect ends m q.1 k zero
    · by_cases hR : RowsDisconnect ends m (middleSwap m q.1) k zero
      · simp [reversalGateBalance, hL, hR]
      · exact (hq ⟨hL, hR⟩).elim
    · by_cases hR : RowsDisconnect ends m (middleSwap m q.1) k zero <;>
        simp [reversalGateBalance, hL, hR]
  by_cases hcn : ReversalGateNegative ends m j k l zero p c
  · have hdp := hcovers c hcn
    rcases hcn with ⟨hLc, hRc⟩
    rcases hdp with ⟨hLd, hRd⟩
    change ¬ RowsDisconnect ends m d.1 k zero at hLd
    change RowsDisconnect ends m (middleSwap m d.1) k zero at hRd
    simp [reversalGateBalance, hLc, hRc, hLd, hRd]
  · by_cases hdn : ReversalGateNegative ends m j k l zero p d
    · have hcp := hcovers d hdn
      rw [hdc] at hcp
      rcases hdn with ⟨hLd, hRd⟩
      rcases hcp with ⟨hLc, hRc⟩
      simp [reversalGateBalance, hLc, hRc, hLd, hRd]
    · exact add_nonneg
        (nonneg_of_not_negative c hcn)
        (nonneg_of_not_negative d hdn)


theorem sum_reversalGateBalance_eq_cycleCutCorrelation
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c₀ : leftSourceMaskFiber ends m j k l zero p) :
    (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c) =
      ∑ z : sourceMaskCycleSpace ends p,
        (bipartitionDisconnectIndicator ends m
            ((rowClass m c₀.1 0 ∆ (z.1.1 ∪ z.2.1)) ∆ p.1) k zero -
          bipartitionDisconnectIndicator ends m
            (rowClass m c₀.1 0 ∆ (z.1.1 ∪ z.2.1)) k zero) := by
  let e := sourceMaskCycleTorsorEquiv ends m j k l zero p c₀
  calc
    _ = ∑ z : sourceMaskCycleSpace ends p,
        reversalGateBalance ends m j k l zero p (e z) := by
      symm
      apply Fintype.sum_equiv e
      intro z
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [reversalGateBalance_eq_bipartitionIndicators]
      have he : e z =
          sourceMaskCycleAction ends m j k l zero p c₀ z := by rfl
      rw [he,
        rowClass_sourceMaskCycleAction_zero]

theorem sum_prop_indicator_eq_card_subtype
    {X : Type*} [Fintype X] (P : X -> Prop) [DecidablePred P]
    [Fintype {x : X // P x}] :
    (∑ x : X, if P x then (1 : ℤ) else 0) =
      Fintype.card {x : X // P x} := by
  rw [Fintype.card_subtype]
  simp


theorem sum_reversalGateBalance_eq_card_sub
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c) =
      (Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) : ℤ) -
        Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) := by
  classical
  rw [show (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c) =
      (∑ c : leftSourceMaskFiber ends m j k l zero p,
        if RowsDisconnect ends m (middleSwap m c.1) k zero
          then (1 : ℤ) else 0) -
        ∑ c : leftSourceMaskFiber ends m j k l zero p,
          if RowsDisconnect ends m c.1 k zero then (1 : ℤ) else 0 by
      simp [reversalGateBalance, Finset.sum_sub_distrib]]
  rw [sum_prop_indicator_eq_card_subtype,
    sum_prop_indicator_eq_card_subtype]
  have hright :
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m (middleSwap m c.1) k zero} =
        Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) :=
    Fintype.card_congr (Equiv.refl _)
  have hleft :
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero} =
        Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hright, hleft]


theorem sum_reversalGateBalance_nonneg_of_equivPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (e : leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (e c)) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c := by
  have hreindex :
      (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p (e c)) =
      ∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c := by
    apply Fintype.sum_equiv e
    intro c
    rfl
  have hsum :
      0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
        (reversalGateBalance ends m j k l zero p c +
          reversalGateBalance ends m j k l zero p (e c)) :=
    Finset.sum_nonneg fun c _ => hpairs c
  rw [Finset.sum_add_distrib, hreindex] at hsum
  omega


theorem sum_reversalGateBalance_nonneg_of_cycleTranslationPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (X Y : Finset I)
    (hX : X ⊆ p.1) (hY : Y ⊆ p.2)
    (hsrcX : sources ends X = ∅) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y
            hX hY hsrcX hsrcY c)) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c :=
  sum_reversalGateBalance_nonneg_of_equivPairs ends m j k l zero p
    (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y
      hX hY hsrcX hsrcY) hpairs


theorem sum_reversalGateBalance_nonneg_of_exists_cycleTranslationCover
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcover : ∃ z : sourceMaskCycleSpace ends p,
      CycleTranslationCoversNegative ends m j k l zero p z) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c := by
  obtain ⟨z, hz⟩ := hcover
  apply sum_reversalGateBalance_nonneg_of_cycleTranslationPairs
    ends m j k l zero p z.1.1 z.2.1
    z.1.2.1 z.2.2.1 z.1.2.2 z.2.2.2
  intro c
  simpa only [sourceMaskCycleAction] using
    cycleTranslation_pairBalance_nonneg_of_coversNegative
      ends m j k l zero p z hz c


theorem sum_reversalGateBalance_nonneg_of_outerCyclePairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (Y : Finset I)
    (hY : Y ⊆ p.2) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY c)) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c :=
  sum_reversalGateBalance_nonneg_of_equivPairs ends m j k l zero p
    (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY) hpairs


end StatMech.GrahamGHS.FourColor
