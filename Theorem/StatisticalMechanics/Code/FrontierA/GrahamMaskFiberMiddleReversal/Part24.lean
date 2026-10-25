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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part27
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalRawCommonClosure_expands_of_collisionTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hemb : CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p) :
    (canonicalRawCommonClosure ends m j k l zero p).card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)).card := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  apply StatMech.FrontierA.card_le_bipartiteNeighbors_of_collisionTokenEmbedding
    R T U
  · simp only [U, StatMech.FrontierA.finiteRelationNeighborhood]
  · refine ⟨canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p,
      canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p, ?_, ?_, ?_⟩
    · exact canonicalStableRawSelfBase_related ends m j k l zero
        hloop hjk hkl hk0 p
    · intro d
      exact ⟨canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p d,
        canonicalStableRawPreferredRightBase_related ends m j k l zero
          hloop hjk hkl hk0 p d⟩
    · simpa only [CanonicalStableRawCollisionTokenEmbedding,
        T, R, U] using hemb

theorem card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hemb : CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion
    ends m j k l zero p
      (canonicalRawCommonClosure_expands_of_collisionTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hemb)

theorem canonicalRawCommonClosure_expands_of_collisionSurplus
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsurplus : CanonicalStableRawCollisionSurplus
      ends m j k l zero p) :
    (canonicalRawCommonClosure ends m j k l zero p).card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)).card := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  apply StatMech.FrontierA.card_le_bipartiteNeighbors_of_collisionSurplus
    R T U
  · simp only [U, StatMech.FrontierA.finiteRelationNeighborhood]
  · simpa only [CanonicalStableRawCollisionSurplus, T, R, U] using hsurplus

theorem card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionSurplus
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsurplus : CanonicalStableRawCollisionSurplus
      ends m j k l zero p) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion
    ends m j k l zero p
      (canonicalRawCommonClosure_expands_of_collisionSurplus
        ends m j k l zero p hsurplus)


theorem card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
        Fintype.card (rightMaskFiber ends m j k l zero p) ↔
      0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c := by
  rw [card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates,
    sum_reversalGateBalance_eq_card_sub]
  omega


theorem card_leftMaskFiber_le_rightMaskFiber_of_canonicalDiscrepancyHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hhall : CanonicalDiscrepancyHall ends m j k l zero p) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) := by
  classical
  obtain ⟨f, -⟩ :=
    (canonicalDiscrepancyHall_iff_exists_matching
      ends m j k l zero p).mp hhall
  have hdisc :
      Fintype.card (negativeReversalGateFiber ends m j k l zero p) ≤
        Fintype.card (positiveReversalGateFiber ends m j k l zero p) :=
    Fintype.card_le_of_embedding f
  have hraw :
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero} ≤
        Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m (middleSwap m c.1) k zero} := by
    rw [StatMech.FrontierA.card_subtype_le_iff_card_leftOnly_le_card_rightOnly]
    calc
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero ∧
              ¬ RowsDisconnect ends m (middleSwap m c.1) k zero} =
          Fintype.card
            (negativeReversalGateFiber ends m j k l zero p) :=
        Fintype.card_congr (Equiv.refl _)
      _ ≤ Fintype.card
          (positiveReversalGateFiber ends m j k l zero p) := hdisc
      _ = Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            ¬ RowsDisconnect ends m c.1 k zero ∧
              RowsDisconnect ends m (middleSwap m c.1) k zero} :=
        Fintype.card_congr (Equiv.refl _)
  apply (card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates
    ends m j k l zero p).2
  calc
    Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) =
        Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero} :=
      Fintype.card_congr (Equiv.refl _)
    _ ≤ Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m (middleSwap m c.1) k zero} := hraw
    _ = Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) :=
      Fintype.card_congr (Equiv.refl _)


theorem card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslationPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (X Y : Finset I)
    (hX : X ⊆ p.1) (hY : Y ⊆ p.2)
    (hsrcX : sources ends X = ∅) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y
            hX hY hsrcX hsrcY c)) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  (card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    ends m j k l zero p).2
      (sum_reversalGateBalance_nonneg_of_cycleTranslationPairs
        ends m j k l zero p X Y hX hY hsrcX hsrcY hpairs)


theorem card_leftMaskFiber_le_rightMaskFiber_of_exists_cycleTranslationCover
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcover : ∃ z : sourceMaskCycleSpace ends p,
      CycleTranslationCoversNegative ends m j k l zero p z) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  (card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    ends m j k l zero p).2
      (sum_reversalGateBalance_nonneg_of_exists_cycleTranslationCover
        ends m j k l zero p hcover)


theorem card_leftMaskFiber_le_rightMaskFiber_of_outerCyclePairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (Y : Finset I)
    (hY : Y ⊆ p.2) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY c)) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  (card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    ends m j k l zero p).2
      (sum_reversalGateBalance_nonneg_of_outerCyclePairs
        ends m j k l zero p Y hY hsrcY hpairs)

end StatMech.GrahamGHS.FourColor
