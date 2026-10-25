/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitNesting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbitPropagation.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbitNesting
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem canonicalTransferUnion_subset_of_adjacentComponentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hnest : CanonicalMaskAdjacentComponentNesting
      ends m j k l zero p)
    (r c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d)
    (hgood : RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero)
        c.1.1) k zero)
    (hbad : ¬ RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero)
        d.1.1) k zero) :
    canonicalTransferUnion ends m k zero d.1.1 ⊆
      canonicalTransferUnion ends m k zero r.1.1 := by
  rw [canonicalTransferUnion, canonicalTransfers_union,
    canonicalTransferUnion, canonicalTransfers_union]
  exact hnest r c d hcd hgood hbad


theorem canonicalMaskAdjacentStrictDescent_of_componentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hnest : CanonicalMaskAdjacentComponentNesting
      ends m j k l zero p) :
    CanonicalMaskAdjacentStrictDescent ends m j k l zero p := by
  intro r c d hcd hgood hbad
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨canonicalTransferUnion_subset_of_adjacentComponentNesting
    ends m j k l zero p hnest r c d hcd hgood hbad, ?_⟩
  intro heq
  have hpairs := canonicalTransfers_eq_of_union_eq_sameMask
    hloop hjk hkl d r heq
  apply hbad
  simpa only [hpairs.1, hpairs.2] using
    canonicalBalancedSwap_disconnects hloop hjk hkl hk0 d.1.2


theorem GrahamFiberMinor_of_canonicalMaskAdjacentComponentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hnest : ∀ p : Finset I × Finset I,
      CanonicalMaskAdjacentComponentNesting ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero :=
  GrahamFiberMinor_of_canonicalMaskAdjacentStrictDescent
    ends m j k l zero hloop hjk hkl hk0
    (fun p => canonicalMaskAdjacentStrictDescent_of_componentNesting
      ends m j k l zero hloop hjk hkl hk0 p (hnest p))

end StatMech.GrahamGHS.FourColor
