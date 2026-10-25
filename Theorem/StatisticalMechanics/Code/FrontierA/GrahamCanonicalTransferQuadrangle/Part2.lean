/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferQuadrangle.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem canonicalMaskTransferAdjacent_quadrangleCompletion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hac : CanonicalTransferWorks ends m k zero a.1.1 c.1.1)
    (hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero) :
    CanonicalMaskTransferAdjacent ends m j k l zero p c
      (canonicalQuadrangleCompletionMemOfDisconnects
        ends m j k l zero hloop hjk hkl p a b c hdisc) := by
  let d := canonicalQuadrangleCompletionMemOfDisconnects
    ends m j k l zero hloop hjk hkl p a b c hdisc
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p a c hac
  refine ⟨q, a, b, rfl, ?_⟩
  change balancedSwap m
      (canonicalMiddleTransfer ends m a.1.1 k zero)
      (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 =
    balancedSwap m
      (canonicalMiddleTransfer ends m b.1.1 k zero)
      (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1
  exact (canonicalTransfer_quadrangleCompletion
    ends m k zero a.1.1 b.1.1 c.1.1).symm


theorem canonicalQuadrangleCompletion_rowCard_eq_transferCard
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero) :
    let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p a b c hdisc;
    #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) =
      #(canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1) := by
  let d := canonicalQuadrangleCompletionMemOfDisconnects
    ends m j k l zero hloop hjk hkl p a b c hdisc
  have hswap : balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1 := by
    exact (canonicalTransfer_quadrangleCompletion
      ends m k zero a.1.1 b.1.1 c.1.1).symm
  have hrow := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl a b c d).mp hswap
  exact card_rowSymmDiff_eq_card_transferSymmDiff_of_translatedRow_eq
    a.1.1 b.1.1 c.1.1 d.1.1 hrow


theorem canonicalQuadrangleCompletion_score_lt_of_rowCard_lt_transferCard
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero)
    (hlt : #(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) <
      #(canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1)) :
    let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p a b c hdisc;
    canonicalCoveragePairScore ends m k zero a.1.1 b.1.1 <
      canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 := by
  let d := canonicalQuadrangleCompletionMemOfDisconnects
    ends m j k l zero hloop hjk hkl p a b c hdisc
  rw [canonicalCoveragePairScore_lt_iff hloop hjk hkl a b c d]
  left
  rw [canonicalQuadrangleCompletion_rowCard_eq_transferCard
    hloop hjk hkl a b c hdisc]
  exact hlt

end StatMech.GrahamGHS.FourColor
