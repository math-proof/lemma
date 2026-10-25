/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferQuadrangle
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem canonicalTransfer_quadrangleCompletion
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4) :
    balancedSwap m
        (canonicalMiddleTransfer ends m b k zero)
        (canonicalOuterTransfer ends m b k zero)
        (canonicalQuadrangleCompletion ends m k zero a b c) =
      balancedSwap m
        (canonicalMiddleTransfer ends m a k zero)
        (canonicalOuterTransfer ends m a k zero) c := by
  rw [canonicalQuadrangleCompletion, balancedSwap_comp_eq_symmDiff]
  simp [canonicalMiddleTransferDifference,
    canonicalOuterTransferDifference]

theorem canonicalQuadrangleCompletion_involutive
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4) :
    canonicalQuadrangleCompletion ends m k zero a b
        (canonicalQuadrangleCompletion ends m k zero a b c) = c := by
  rw [canonicalQuadrangleCompletion, canonicalQuadrangleCompletion,
    balancedSwap_involutive]


theorem canonicalQuadrangleCompletion_comm
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4) :
    canonicalQuadrangleCompletion ends m k zero a b c =
      canonicalQuadrangleCompletion ends m k zero b a c := by
  have hmiddle : canonicalMiddleTransferDifference ends m k zero a b =
      canonicalMiddleTransferDifference ends m k zero b a := by
    exact symmDiff_comm _ _
  have houter : canonicalOuterTransferDifference ends m k zero a b =
      canonicalOuterTransferDifference ends m k zero b a := by
    exact symmDiff_comm _ _
  rw [canonicalQuadrangleCompletion, canonicalQuadrangleCompletion,
    hmiddle, houter]


theorem canonicalQuadrangleCompletion_trans
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c d : ↑m -> Fin 4) :
    canonicalQuadrangleCompletion ends m k zero b c
        (canonicalQuadrangleCompletion ends m k zero a b d) =
      canonicalQuadrangleCompletion ends m k zero a c d := by
  rw [canonicalQuadrangleCompletion, canonicalQuadrangleCompletion,
    canonicalQuadrangleCompletion, balancedSwap_comp_eq_symmDiff]
  simp only [canonicalMiddleTransferDifference,
    canonicalOuterTransferDifference]
  have hmiddle :
      (canonicalMiddleTransfer ends m a k zero ∆
          canonicalMiddleTransfer ends m b k zero) ∆
        (canonicalMiddleTransfer ends m b k zero ∆
          canonicalMiddleTransfer ends m c k zero) =
        canonicalMiddleTransfer ends m a k zero ∆
          canonicalMiddleTransfer ends m c k zero := by
    calc
      _ = canonicalMiddleTransfer ends m a k zero ∆
          (canonicalMiddleTransfer ends m b k zero ∆
            canonicalMiddleTransfer ends m b k zero) ∆
          canonicalMiddleTransfer ends m c k zero := by ac_rfl
      _ = _ := by simp
  have houter :
      (canonicalOuterTransfer ends m a k zero ∆
          canonicalOuterTransfer ends m b k zero) ∆
        (canonicalOuterTransfer ends m b k zero ∆
          canonicalOuterTransfer ends m c k zero) =
        canonicalOuterTransfer ends m a k zero ∆
          canonicalOuterTransfer ends m c k zero := by
    calc
      _ = canonicalOuterTransfer ends m a k zero ∆
          (canonicalOuterTransfer ends m b k zero ∆
            canonicalOuterTransfer ends m b k zero) ∆
          canonicalOuterTransfer ends m c k zero := by ac_rfl
      _ = _ := by simp
  rw [hmiddle, houter]


theorem canonicalQuadrangleCompletion_changes_commute
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b r s x : ↑m -> Fin 4) :
    canonicalQuadrangleCompletion ends m k zero a b
        (canonicalQuadrangleCompletion ends m k zero r s x) =
      canonicalQuadrangleCompletion ends m k zero r s
        (canonicalQuadrangleCompletion ends m k zero a b x) := by
  unfold canonicalQuadrangleCompletion
  rw [balancedSwap_comp_eq_symmDiff, balancedSwap_comp_eq_symmDiff]
  rw [symmDiff_comm
    (canonicalMiddleTransferDifference ends m k zero r s)
    (canonicalMiddleTransferDifference ends m k zero a b)]
  rw [symmDiff_comm
    (canonicalOuterTransferDifference ends m k zero r s)
    (canonicalOuterTransferDifference ends m k zero a b)]


theorem canonicalTransferWorks_quadrangleCompletion
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4)
    (hac : CanonicalTransferWorks ends m k zero a c) :
    CanonicalTransferWorks ends m k zero b
      (canonicalQuadrangleCompletion ends m k zero a b c) := by
  unfold CanonicalTransferWorks at hac ⊢
  rw [canonicalTransfer_quadrangleCompletion]
  exact hac


theorem canonicalTransferWorks_quadrangleCompletion_iff
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4) :
    CanonicalTransferWorks ends m k zero a
        (canonicalQuadrangleCompletion ends m k zero a b c) ↔
      CanonicalTransferWorks ends m k zero b c := by
  constructor
  · intro h
    have h' := canonicalTransferWorks_quadrangleCompletion
      ends m k zero a b
        (canonicalQuadrangleCompletion ends m k zero a b c) h
    rwa [canonicalQuadrangleCompletion_involutive] at h'
  · intro h
    have h' := canonicalTransferWorks_quadrangleCompletion
      ends m k zero b a c h
    rwa [← canonicalQuadrangleCompletion_comm] at h'


theorem canonicalTransferWorks_new_quadrangleCompletion_iff
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4) :
    CanonicalTransferWorks ends m k zero b
        (canonicalQuadrangleCompletion ends m k zero a b c) ↔
      CanonicalTransferWorks ends m k zero a c := by
  rw [canonicalQuadrangleCompletion_comm]
  exact canonicalTransferWorks_quadrangleCompletion_iff
    ends m k zero b a c


theorem leftPattern_of_sourceless_balancedSwap
    {ends : I -> Sym2 W} {m X Y : Finset I}
    {A B : Finset W} {u v : W} {c : ↑m -> Fin 4}
    (hleft : LeftPattern ends m A B u v c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
    (hsrcX : sources ends X = ∅)
    (hsrcY : sources ends Y = ∅)
    (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
    LeftPattern ends m A B u v (balancedSwap m X Y c) := by
  rcases hleft with ⟨h0, h1, h2, h3, -⟩
  have hY' : Y ⊆ colorClass m (middleSwapOn m X c) 0 ∪
      colorClass m (middleSwapOn m X c) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  unfold balancedSwap
  refine ⟨?_, ?_, ?_, ?_, hdisc⟩
  · rw [colorClass_outerSwapOn_zero m Y _ hY', sources_symmDiff,
      colorClass_middleSwapOn_zero, h0, hsrcY]
    simp
  · rw [colorClass_outerSwapOn_one, colorClass_middleSwapOn_one m X c hX,
      sources_symmDiff, h1, hsrcX]
    simp
  · rw [colorClass_outerSwapOn_two, colorClass_middleSwapOn_two m X c hX,
      sources_symmDiff, h2, hsrcX]
    simp
  · rw [colorClass_outerSwapOn_three m Y _ hY', sources_symmDiff,
      colorClass_middleSwapOn_three, h3, hsrcY]
    simp

theorem symmDiff_subset_of_subsets
    {A B S : Finset I} (hA : A ⊆ S) (hB : B ⊆ S) : A ∆ B ⊆ S := by
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with hi | hi
  · exact hA hi.1
  · exact hB hi.1


end StatMech.GrahamGHS.FourColor
