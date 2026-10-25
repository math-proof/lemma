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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part15
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalRawCommonClosure_fixed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    StatMech.FrontierA.finiteCommonClosureStep
        (fun c : leftSourceMaskFiber ends m j k l zero p =>
          RowsDisconnect ends m c.1 k zero)
        (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) =
      canonicalRawCommonClosure ends m j k l zero p := by
  have hfixed := (Classical.choose_spec
    (exists_canonicalRawCommonClosureIter_fixed ends m j k l zero p)).2
  change canonicalRawCommonClosureIter ends m j k l zero p
      (canonicalRawCommonClosureIndex ends m j k l zero p + 1) =
    canonicalRawCommonClosureIter ends m j k l zero p
      (canonicalRawCommonClosureIndex ends m j k l zero p)
  exact hfixed

theorem canonicalRawNegativeGateFinset_subset_commonClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    canonicalRawNegativeGateFinset ends m j k l zero p ⊆
      canonicalRawCommonClosure ends m j k l zero p :=
  StatMech.FrontierA.finiteCommonClosureIter_zero_subset _ _ _ _ _

theorem canonicalRawCommonClosure_leftGate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    ∀ c ∈ canonicalRawCommonClosure ends m j k l zero p,
      RowsDisconnect ends m c.1 k zero := by
  classical
  apply StatMech.FrontierA.finiteCommonClosureIter_preserves_left
  intro c hc
  have hneg : ReversalGateNegative ends m j k l zero p c := by
    simpa only [canonicalRawNegativeGateFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hc
  exact hneg.1


theorem canonicalRawCommonClosure_common_mem_neighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hc : c ∈ canonicalRawCommonClosure ends m j k l zero p)
    (hcRight : RowsDisconnect ends m (middleSwap m c.1) k zero) :
    c ∈ StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p) := by
  classical
  apply StatMech.FrontierA.finiteCommonClosureIter_common_mem_neighborhood
    (fun c : leftSourceMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m c.1 k zero)
    (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawNegativeGateFinset ends m j k l zero p)
    ?_ (canonicalRawCommonClosureIndex ends m j k l zero p) c hc hcRight
  intro x hx
  have hnegative : ReversalGateNegative ends m j k l zero p x := by
    simpa only [canonicalRawNegativeGateFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hx
  exact hnegative.2


theorem canonicalRawCommonClosure_right_iff_neighborhood_left
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    (c ∈ canonicalRawCommonClosure ends m j k l zero p ∧
        RowsDisconnect ends m (middleSwap m c.1) k zero) ↔
      (c ∈ StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) ∧
          RowsDisconnect ends m c.1 k zero) := by
  classical
  constructor
  · intro hc
    rcases hc with ⟨hcClosure, hcRight⟩
    exact ⟨
      canonicalRawCommonClosure_common_mem_neighborhood
        ends m j k l zero p c hcClosure hcRight,
      canonicalRawCommonClosure_leftGate
        ends m j k l zero p c hcClosure⟩
  · intro hc
    rcases hc with ⟨hcNeighborhood, hcLeft⟩
    obtain ⟨source, hsource, hrelated⟩ :=
      (Finset.mem_filter.mp hcNeighborhood).2
    obtain ⟨_, hcRight, _⟩ := hrelated
    have hcStep : c ∈ StatMech.FrontierA.finiteCommonClosureStep
        (fun c : leftSourceMaskFiber ends m j k l zero p =>
          RowsDisconnect ends m c.1 k zero)
        (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) :=
      (StatMech.FrontierA.mem_finiteCommonClosureStep _ _ _ _ c).mpr
        (Or.inr ⟨hcNeighborhood, hcLeft, hcRight⟩)
    rw [canonicalRawCommonClosure_fixed ends m j k l zero p] at hcStep
    exact ⟨hcStep, hcRight⟩


end StatMech.GrahamGHS.FourColor
