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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part16
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem card_canonicalNegativeFullNeighborhood_eq_parts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    (canonicalNegativeFullNeighborhood ends m j k l zero p S).card =
      (canonicalNegativePositiveNeighborhood
        ends m j k l zero p S).card +
      (canonicalNegativeCommonNeighborhood
        ends m j k l zero p S).card := by
  classical
  let U := canonicalNegativeFullNeighborhood ends m j k l zero p S
  let common := fun q : rightMaskFiber ends m j k l zero p =>
    RowsDisconnect ends m
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p q).1.1 k zero
  have hsplit := U.card_filter_add_card_filter_not common
  simpa only [canonicalNegativePositiveNeighborhood,
    canonicalNegativeCommonNeighborhood, U, common, add_comm] using hsplit.symm


theorem positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p))
    (q : positiveReversalGateFiber ends m j k l zero p) :
    positiveReversalGateToRightMaskFiber ends m j k l zero p q ∈
        canonicalNegativePositiveNeighborhood ends m j k l zero p S ↔
      ∃ c ∈ S,
        CanonicalDiscrepancyRelated ends m j k l zero p c q := by
  classical
  simp only [canonicalNegativePositiveNeighborhood, Finset.mem_filter,
    canonicalNegativeFullNeighborhood,
    mem_canonicalMaskRightNeighborhood_iff,
    liftedNegativeReversalGateFamily, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ⟨c, hc, rfl⟩, ha⟩, -⟩
    exact ⟨c, hc, ha⟩
  · rintro ⟨c, hc, hq⟩
    refine ⟨⟨negativeReversalGateToLeftMaskFiber
      ends m j k l zero p c, ⟨c, hc, rfl⟩, hq⟩, ?_⟩
    simpa [positiveReversalGateToRightMaskFiber] using q.2.1

end StatMech.GrahamGHS.FourColor
