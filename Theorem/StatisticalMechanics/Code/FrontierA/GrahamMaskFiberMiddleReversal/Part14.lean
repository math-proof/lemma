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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part17
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem image_canonicalDiscrepancyNeighborhood_eq_positiveNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    transportedCanonicalDiscrepancyNeighborhood
        ends m j k l zero p S =
      canonicalNegativePositiveNeighborhood ends m j k l zero p S := by
  classical
  unfold transportedCanonicalDiscrepancyNeighborhood
  ext q
  constructor
  · intro hq
    obtain ⟨qpos, hqpos, rfl⟩ := Finset.mem_image.mp hq
    apply (positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff
      ends m j k l zero p S qpos).mpr
    simpa only [canonicalDiscrepancyNeighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and] using hqpos
  · intro hq
    let pulled := rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p q
    have hnot : ¬ RowsDisconnect ends m pulled.1.1 k zero :=
      (Finset.mem_filter.mp hq).2
    let qpos : positiveReversalGateFiber ends m j k l zero p :=
      ⟨pulled.1, hnot, pulled.2⟩
    have heq : positiveReversalGateToRightMaskFiber
        ends m j k l zero p qpos = q := by
      dsimp only [qpos, pulled, positiveReversalGateToRightMaskFiber]
      exact (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p).symm_apply_apply q
    have hrelated : ∃ c ∈ S,
        CanonicalDiscrepancyRelated ends m j k l zero p c qpos :=
      (positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff
        ends m j k l zero p S qpos).mp (heq ▸ hq)
    apply Finset.mem_image.mpr
    refine ⟨qpos, ?_, heq⟩
    simpa only [canonicalDiscrepancyNeighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and] using hrelated

theorem card_canonicalNegativePositiveNeighborhood_eq_discrepancy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    (canonicalNegativePositiveNeighborhood ends m j k l zero p S).card =
      (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card := by
  classical
  rw [← image_canonicalDiscrepancyNeighborhood_eq_positiveNeighborhood]
  unfold transportedCanonicalDiscrepancyNeighborhood
  apply Finset.card_image_of_injective
  intro q r hqr
  apply Subtype.ext
  have h := congrArg
    (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p) hqr
  have hval := congrArg Subtype.val h
  simpa [positiveReversalGateToRightMaskFiber] using hval


theorem card_canonicalNegativeFullNeighborhood_eq_discrepancy_add_common
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    (canonicalNegativeFullNeighborhood ends m j k l zero p S).card =
      (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card +
      (canonicalNegativeCommonNeighborhood ends m j k l zero p S).card := by
  rw [card_canonicalNegativeFullNeighborhood_eq_parts,
    card_canonicalNegativePositiveNeighborhood_eq_discrepancy]


end StatMech.GrahamGHS.FourColor
