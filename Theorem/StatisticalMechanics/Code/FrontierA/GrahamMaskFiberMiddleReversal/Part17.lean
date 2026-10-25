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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part20
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalDiscrepancyReferenceSelector_works
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsingle : CanonicalDiscrepancySingletonExpansion
      ends m j k l zero p)
    (c : negativeReversalGateFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero
      (canonicalDiscrepancyReferenceSelector
        ends m j k l zero p hsingle c).1.1
      (negativeReversalGateToLeftMaskFiber
        ends m j k l zero p c).1.1 :=
  (Classical.choose_spec ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p
      (negativeReversalGateToLeftMaskFiber ends m j k l zero p c)
      (positiveReversalGateToRightMaskFiber ends m j k l zero p
        (canonicalDiscrepancyTargetSelector
          ends m j k l zero p hsingle c))).mp
    (canonicalDiscrepancyTargetSelector_related
      ends m j k l zero p hsingle c))).1


theorem card_le_canonicalDiscrepancyNeighborhood_of_card_le_one
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsingle : CanonicalDiscrepancySingletonExpansion
      ends m j k l zero p)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p))
    (hcard : S.card ≤ 1) :
    S.card ≤
      (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨c, hc⟩ := hS
    have hSeq : S = {c} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hc, ?_⟩
      intro d hd
      exact (Finset.card_le_one.mp hcard) d hd c hc
    subst S
    let q := canonicalDiscrepancyTargetSelector
      ends m j k l zero p hsingle c
    have hq : q ∈ canonicalDiscrepancyNeighborhood
        ends m j k l zero p {c} := by
      simp only [canonicalDiscrepancyNeighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨c, rfl,
        canonicalDiscrepancyTargetSelector_related
          ends m j k l zero p hsingle c⟩
    simpa using (Finset.card_pos.mpr ⟨q, hq⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp


theorem canonicalDiscrepancyHall_iff_exists_matching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    CanonicalDiscrepancyHall ends m j k l zero p ↔
      ∃ f : negativeReversalGateFiber ends m j k l zero p ↪
          positiveReversalGateFiber ends m j k l zero p,
        ∀ c, CanonicalDiscrepancyRelated ends m j k l zero p c (f c) := by
  classical
  let rel := CanonicalDiscrepancyRelated ends m j k l zero p
  have hhall := Fintype.all_card_le_filter_rel_iff_exists_injective rel
  constructor
  · intro h
    have h' : ∀ S : Finset
        (negativeReversalGateFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card := by
      simpa only [CanonicalDiscrepancyHall,
        canonicalDiscrepancyNeighborhood] using h
    obtain ⟨f, hf, himage⟩ := hhall.mp h'
    exact ⟨⟨f, hf⟩, himage⟩
  · rintro ⟨f, himage⟩
    have h' : ∀ S : Finset
        (negativeReversalGateFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card :=
      hhall.mpr ⟨f, f.injective, himage⟩
    simpa only [CanonicalDiscrepancyHall,
      canonicalDiscrepancyNeighborhood] using h'


theorem card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
        Fintype.card (rightMaskFiber ends m j k l zero p) ↔
      Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) ≤
        Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) := by
  rw [Fintype.card_congr
      (leftMaskFiberEquivSourceMaskGateFiber ends m j k l zero p),
    Fintype.card_congr
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p)]


theorem card_leftMaskFiber_le_rightMaskFiber_iff_discrepancies
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
        Fintype.card (rightMaskFiber ends m j k l zero p) ↔
      Fintype.card (negativeReversalGateFiber ends m j k l zero p) ≤
        Fintype.card (positiveReversalGateFiber ends m j k l zero p) := by
  classical
  rw [card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates]
  unfold leftSourceMaskGateFiber reversedRightSourceMaskGateFiber
    negativeReversalGateFiber positiveReversalGateFiber
    ReversalGateNegative ReversalGatePositive
  rw [Fintype.card_subtype, Fintype.card_subtype,
    Fintype.card_subtype, Fintype.card_subtype]
  let leftGate := Finset.univ.filter fun
    c : leftSourceMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m c.1 k zero
  let rightGate := Finset.univ.filter fun
    c : leftSourceMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m (middleSwap m c.1) k zero
  have hnegative : Finset.univ.filter (fun
      c : leftSourceMaskFiber ends m j k l zero p =>
        RowsDisconnect ends m c.1 k zero ∧
          ¬ RowsDisconnect ends m (middleSwap m c.1) k zero) =
      leftGate \ rightGate := by
    ext c
    simp [leftGate, rightGate]
  have hpositive : Finset.univ.filter (fun
      c : leftSourceMaskFiber ends m j k l zero p =>
        ¬ RowsDisconnect ends m c.1 k zero ∧
          RowsDisconnect ends m (middleSwap m c.1) k zero) =
      rightGate \ leftGate := by
    ext c
    simp [leftGate, rightGate, and_comm]
  rw [hnegative, hpositive]
  change leftGate.card ≤ rightGate.card ↔
    (leftGate \ rightGate).card ≤ (rightGate \ leftGate).card
  have hleft := Finset.card_sdiff_add_card leftGate rightGate
  have hright := Finset.card_sdiff_add_card rightGate leftGate
  rw [Finset.union_comm rightGate leftGate] at hright
  omega


theorem card_leftMaskFiber_le_rightMaskFiber_of_commonClosedRawExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (T : Finset (leftSourceMaskFiber ends m j k l zero p))
    (hnegative : canonicalRawNegativeGateFinset
      ends m j k l zero p ⊆ T)
    (hleft : ∀ c ∈ T, RowsDisconnect ends m c.1 k zero)
    (hclosed : StatMech.FrontierA.finiteCommonClosureStep
        (fun c : leftSourceMaskFiber ends m j k l zero p =>
          RowsDisconnect ends m c.1 k zero)
        (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
        (CanonicalRawGateRelated ends m j k l zero p) T = T)
    (hexpand : T.card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p) T).card) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) := by
  classical
  let P := fun c : leftSourceMaskFiber ends m j k l zero p =>
    RowsDisconnect ends m c.1 k zero
  let Q := fun c : leftSourceMaskFiber ends m j k l zero p =>
    RowsDisconnect ends m (middleSwap m c.1) k zero
  let R := CanonicalRawGateRelated ends m j k l zero p
  have hrel : ∀ {c d}, R c d -> P c ∧ Q d := by
    rintro c d ⟨hc, hd, -⟩
    exact ⟨hc, hd⟩
  have hcount :=
    StatMech.FrontierA.card_leftOnly_le_rightOnly_of_commonClosed_expansion
      P Q R T hrel (by
        simpa only [P, Q, canonicalRawNegativeGateFinset,
          ReversalGateNegative] using hnegative) (by
        simpa only [P] using hleft) (by
        simpa only [P, Q, R] using hclosed) (by
        simpa only [R] using hexpand)
  apply (card_leftMaskFiber_le_rightMaskFiber_iff_discrepancies
    ends m j k l zero p).mpr
  unfold negativeReversalGateFiber positiveReversalGateFiber
    ReversalGateNegative ReversalGatePositive
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simpa only [P, Q] using hcount


theorem card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hexpand :
      (canonicalRawCommonClosure ends m j k l zero p).card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (canonicalRawCommonClosure ends m j k l zero p)).card) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  card_leftMaskFiber_le_rightMaskFiber_of_commonClosedRawExpansion
    ends m j k l zero p
      (canonicalRawCommonClosure ends m j k l zero p)
      (canonicalRawNegativeGateFinset_subset_commonClosure
        ends m j k l zero p)
      (canonicalRawCommonClosure_leftGate ends m j k l zero p)
      (canonicalRawCommonClosure_fixed ends m j k l zero p) hexpand


end StatMech.GrahamGHS.FourColor
