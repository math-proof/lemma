/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalReferenceNeighborhoodEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (hworks : ∀ c ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ↑S ↪ ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) where
  toFun c := by
    let q := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r c.1 (hworks c.1 c.2)
    refine ⟨q, (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨c.1, c.2, ?_⟩⟩
    exact (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c.1 q).mpr ⟨r, hworks c.1 c.2, rfl⟩
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hraw := congrArg
      (fun q : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S) => q.1.1.1) hcd
    change balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) d.1.1.1 at hraw
    have hinv := congrArg
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero)) hraw
    simpa only [balancedSwap_involutive] using hinv


end StatMech.GrahamGHS.FourColor
