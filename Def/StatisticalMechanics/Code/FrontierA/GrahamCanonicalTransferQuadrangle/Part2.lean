/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferQuadrangle
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

noncomputable def canonicalQuadrangleCompletionMemOfDisconnects
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero) :
    leftMaskFiber ends m j k l zero p := by
  let X := canonicalMiddleTransferDifference ends m k zero a.1.1 b.1.1
  let Y := canonicalOuterTransferDifference ends m k zero a.1.1 b.1.1
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1
  have hva := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  have hvb := canonicalTransfers_valid_on_sameMask hloop hjk hkl b c
  have hX : X ⊆ colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 :=
    symmDiff_subset_of_subsets hva.1 hvb.1
  have hY : Y ⊆ colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 :=
    symmDiff_subset_of_subsets hva.2.1 hvb.2.1
  have hsrcX : sources ends X = ∅ := by
    dsimp only [X, canonicalMiddleTransferDifference]
    rw [sources_symmDiff, hva.2.2.1, hvb.2.2.1]
    exact symmDiff_self _
  have hsrcY : sources ends Y = ∅ := by
    dsimp only [Y, canonicalOuterTransferDifference]
    rw [sources_symmDiff, hva.2.2.2, hvb.2.2.2]
    exact symmDiff_self _
  have hd : LeftPattern ends m {j, k} {k, l} k zero d := by
    apply leftPattern_of_sourceless_balancedSwap c.1.2 hX hY hsrcX hsrcY
    simpa only [d, X, Y, canonicalQuadrangleCompletion] using hdisc
  refine ⟨⟨d, hd⟩, ?_⟩
  calc
    fourColorMaskProfile m d = fourColorMaskProfile m c.1.1 := by
      simp [d, canonicalQuadrangleCompletion,
        fourColorMaskProfile_balancedSwap]
    _ = p := c.2


end StatMech.GrahamGHS.FourColor
