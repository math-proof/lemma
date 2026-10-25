/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part14
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem rightPattern_of_middleTransfer {ends : ι → Sym2 W} {m X : Finset ι}
    {A B : Finset W} {u v : W} {c : ↑m → Fin 4}
    (hleft : LeftPattern ends m A B u v c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hsrc : Sharpness.RandomCurrent.sources ends X = B)
    (hdisc : RowsDisconnect ends m (middleSwapOn m X c) u v) :
    RightPattern ends m A B u v (middleSwapOn m X c) := by
  rcases hleft with ⟨h0, h1, h2, h3, -⟩
  refine ⟨?_, ?_, ?_, ?_, hdisc⟩
  · rw [colorClass_middleSwapOn_zero]
    exact h0
  · rw [colorClass_middleSwapOn_one m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h1, hsrc]
    simp
  · rw [colorClass_middleSwapOn_two m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h2, hsrc]
    simpa using (symmDiff_self B)
  · rw [colorClass_middleSwapOn_three]
    exact h3


theorem rightPattern_of_balancedTransfer {ends : ι → Sym2 W} {m X Y : Finset ι}
    {A B : Finset W} {u v : W} {c : ↑m → Fin 4}
    (hleft : LeftPattern ends m A B u v c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
    (hsrcX : Sharpness.RandomCurrent.sources ends X = B)
    (hsrcY : Sharpness.RandomCurrent.sources ends Y = ∅)
    (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
    RightPattern ends m A B u v (balancedSwap m X Y c) := by
  rcases hleft with ⟨h0, h1, h2, h3, -⟩
  have hY' : Y ⊆ colorClass m (middleSwapOn m X c) 0 ∪
      colorClass m (middleSwapOn m X c) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  unfold balancedSwap
  refine ⟨?_, ?_, ?_, ?_, hdisc⟩
  · rw [colorClass_outerSwapOn_zero m Y _ hY',
      Sharpness.RandomCurrent.sources_symmDiff, colorClass_middleSwapOn_zero, h0, hsrcY]
    simp
  · rw [colorClass_outerSwapOn_one, colorClass_middleSwapOn_one m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h1, hsrcX]
    simp
  · rw [colorClass_outerSwapOn_two, colorClass_middleSwapOn_two m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h2, hsrcX]
    simpa using (symmDiff_self B)
  · rw [colorClass_outerSwapOn_three m Y _ hY',
      Sharpness.RandomCurrent.sources_symmDiff, colorClass_middleSwapOn_three, h3, hsrcY]
    simp


theorem leftPattern_sharedSource_connections {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    Sharpness.RandomCurrent.connK ends (colorClass m c 0) j k ∧
      Sharpness.RandomCurrent.connK ends (colorClass m c 2) k l := by
  constructor
  · apply Walls.gc6_pairingPath_abstract ends (colorClass m c 0) (colorClass m c 0)
    · intro i hi
      exact hloop i (colorClass_subset m c 0 hi)
    · exact Finset.Subset.rfl
    · exact h.1
    · exact hjk
  · apply Walls.gc6_pairingPath_abstract ends (colorClass m c 2) (colorClass m c 2)
    · intro i hi
      exact hloop i (colorClass_subset m c 2 hi)
    · exact Finset.Subset.rfl
    · exact h.2.2.1
    · exact hkl


theorem leftPattern_sharedSource_avoids_zero {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 0) j zero ∧
      ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 1) l zero := by
  have hp := leftPattern_sharedSource_connections hloop hjk hkl h
  rcases h with ⟨_, _, _, _, hdisc⟩
  have hjkRow : Sharpness.RandomCurrent.connK ends (rowClass m c 0) j k := by
    rw [rowClass_zero]
    exact connK_mono (Finset.subset_union_left) hp.1
  have hklRow : Sharpness.RandomCurrent.connK ends (rowClass m c 1) k l := by
    rw [rowClass_one]
    exact connK_mono (Finset.subset_union_left) hp.2
  constructor
  · intro hjzero
    exact hdisc.1 ((Sharpness.RandomCurrent.connK_symm ends _ hjkRow).trans hjzero)
  · intro hlzero
    exact hdisc.2 (hklRow.trans hlzero)


theorem canonicalTransfers_valid {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    canonicalMiddleTransfer ends m c k zero ⊆
        colorClass m c 1 ∪ colorClass m c 2 ∧
      canonicalOuterTransfer ends m c k zero ⊆
        colorClass m c 0 ∪ colorClass m c 3 ∧
      Sharpness.RandomCurrent.sources ends (canonicalMiddleTransfer ends m c k zero) =
        {k, l} ∧
      Sharpness.RandomCurrent.sources ends (canonicalOuterTransfer ends m c k zero) = ∅ := by
  classical
  have hconn := leftPattern_sharedSource_connections hloop hjk hkl h
  have hav := leftPattern_sharedSource_avoids_zero hloop hjk hkl h
  have hC0 : colorClass m c 0 ⊆ rowClass m c 0 := by
    rw [rowClass_zero]
    exact Finset.subset_union_left
  have hC1 : colorClass m c 1 ⊆ rowClass m c 0 := by
    rw [rowClass_zero]
    exact Finset.subset_union_right
  have hC2 : colorClass m c 2 ⊆ rowClass m c 1 := by
    rw [rowClass_one]
    exact Finset.subset_union_left
  have hC3 : colorClass m c 3 ⊆ rowClass m c 1 := by
    rw [rowClass_one]
    exact Finset.subset_union_right
  have hsrc1 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 1 ∩ edgeComponent ends (rowClass m c 0) zero) = ∅ := by
    rw [sources_inter_edgeComponent hC1, h.2.1]
    simp
  have hsrc2 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 2 ∩ edgeComponent ends (rowClass m c 1) k) = {k, l} := by
    rw [sources_inter_edgeComponent hC2, h.2.2.1]
    apply Finset.inter_eq_left.mpr
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Sharpness.RandomCurrent.mem_compOf]
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · rw [rowClass_one]
      exact connK_mono Finset.subset_union_left hconn.2
  have hsrc0 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 0 ∩ edgeComponent ends (rowClass m c 0) zero) = ∅ := by
    rw [sources_inter_edgeComponent hC0, h.1]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
    rw [Sharpness.RandomCurrent.mem_compOf] at hcomp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hav.1 (Sharpness.RandomCurrent.connK_symm ends _ hcomp)
    · exact h.2.2.2.2.1 (Sharpness.RandomCurrent.connK_symm ends _ hcomp)
  have hsrc3 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 3 ∩ edgeComponent ends (rowClass m c 1) k) = ∅ := by
    rw [sources_inter_edgeComponent hC3, h.2.2.2.1]
    simp
  have hd12 : Disjoint
      (colorClass m c 1 ∩ edgeComponent ends (rowClass m c 0) zero)
      (colorClass m c 2 ∩ edgeComponent ends (rowClass m c 1) k) :=
    (colorClass_disjoint m c (show (1 : Fin 4) ≠ 2 by decide)).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hd03 : Disjoint
      (colorClass m c 0 ∩ edgeComponent ends (rowClass m c 0) zero)
      (colorClass m c 3 ∩ edgeComponent ends (rowClass m c 1) k) :=
    (colorClass_disjoint m c (show (0 : Fin 4) ≠ 3 by decide)).mono
      Finset.inter_subset_left Finset.inter_subset_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).1
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).1
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).1
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).1
  · rw [canonicalMiddleTransfer, sources_union_of_disjoint hd12, hsrc1, hsrc2]
    simp
  · rw [canonicalOuterTransfer, sources_union_of_disjoint hd03, hsrc0, hsrc3]
    simp

theorem canonicalTransfers_union {ends : ι → Sym2 W} {m : Finset ι}
    {k zero : W} {c : ↑m → Fin 4} :
    canonicalMiddleTransfer ends m c k zero ∪ canonicalOuterTransfer ends m c k zero =
      edgeComponent ends (rowClass m c 0) zero ∪
        edgeComponent ends (rowClass m c 1) k := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi <;>
      rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).2
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).2
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · have hirow : i ∈ rowClass m c 0 := by
        rw [edgeComponent, Finset.mem_filter] at hi
        exact hi.1
      rw [rowClass_zero, Finset.mem_union] at hirow
      rcases hirow with hi0 | hi1
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi0, hi⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi1, hi⟩))
    · have hirow : i ∈ rowClass m c 1 := by
        rw [edgeComponent, Finset.mem_filter] at hi
        exact hi.1
      rw [rowClass_one, Finset.mem_union] at hirow
      rcases hirow with hi2 | hi3
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi2, hi⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi3, hi⟩))

theorem symmDiff_componentExchange_first {K L A B : Finset ι}
    (hA : A ⊆ K) (hB : B ⊆ L) (hKL : Disjoint K L) :
    K ∆ (A ∪ B) = (K \ A) ∪ B := by
  ext i
  have hAi := @hA i
  have hBi := @hB i
  rw [Finset.disjoint_left] at hKL
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  aesop

theorem symmDiff_componentExchange_second {K L A B : Finset ι}
    (hA : A ⊆ K) (hB : B ⊆ L) (hKL : Disjoint K L) :
    L ∆ (A ∪ B) = (L \ B) ∪ A := by
  rw [Finset.union_comm]
  exact symmDiff_componentExchange_first hB hA hKL.symm


theorem canonicalBalancedSwap_rows {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    rowClass m (balancedSwap m (canonicalMiddleTransfer ends m c k zero)
        (canonicalOuterTransfer ends m c k zero) c) 0 =
        exchangeFirstRow ends (rowClass m c 0) (rowClass m c 1) k zero ∧
      rowClass m (balancedSwap m (canonicalMiddleTransfer ends m c k zero)
        (canonicalOuterTransfer ends m c k zero) c) 1 =
        exchangeSecondRow ends (rowClass m c 0) (rowClass m c 1) k zero := by
  classical
  have hv := canonicalTransfers_valid hloop hjk hkl h
  have hE0 : edgeComponent ends (rowClass m c 0) zero ⊆ rowClass m c 0 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1 : edgeComponent ends (rowClass m c 1) k ⊆ rowClass m c 1 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hrows : Disjoint (rowClass m c 0) (rowClass m c 1) := by
    rw [Finset.disjoint_left]
    intro i hi0 hi1
    rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
    exact hi1.2 hi0
  constructor
  · rw [rowClass_balancedSwap_zero hv.1 hv.2.1, canonicalTransfers_union,
      exchangeFirstRow]
    exact symmDiff_componentExchange_first hE0 hE1 hrows
  · rw [rowClass_balancedSwap_one hv.1 hv.2.1, canonicalTransfers_union,
      exchangeSecondRow]
    exact symmDiff_componentExchange_second hE0 hE1 hrows

theorem canonicalBalancedSwap_disconnects {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    RowsDisconnect ends m
      (balancedSwap m (canonicalMiddleTransfer ends m c k zero)
        (canonicalOuterTransfer ends m c k zero) c) k zero := by
  rw [RowsDisconnect]
  have hrows := canonicalBalancedSwap_rows hloop hjk hkl h
  rw [hrows.1, hrows.2]
  exact componentExchange_disconnects hk0 h.2.2.2.2.1 h.2.2.2.2.2


theorem leftPattern_componentExchange_disconnects {ends : ι → Sym2 W} {m : Finset ι}
    {A B : Finset W} {k zero : W} {c : ↑m → Fin 4} (hk0 : k ≠ zero)
    (h : LeftPattern ends m A B k zero c) :
    ¬ Sharpness.RandomCurrent.connK ends
        (exchangeFirstRow ends (rowClass m c 0) (rowClass m c 1) k zero) k zero ∧
      ¬ Sharpness.RandomCurrent.connK ends
        (exchangeSecondRow ends (rowClass m c 0) (rowClass m c 1) k zero) k zero :=
  componentExchange_disconnects hk0 h.2.2.2.2.1 h.2.2.2.2.2


theorem leftPattern_rowBoundaries {ends : ι → Sym2 W} {m : Finset ι} {A B : Finset W}
    {u v : W} {c : ↑m → Fin 4} (h : LeftPattern ends m A B u v c) :
    Sharpness.RandomCurrent.sources ends (rowClass m c 0) = A ∧
      Sharpness.RandomCurrent.sources ends (rowClass m c 1) = B := by
  rcases h with ⟨h0, h1, h2, h3, -⟩
  constructor
  · rw [rowClass_zero]
    have hd := colorClass_disjoint m c (show (0 : Fin 4) ≠ 1 by decide)
    have hu : colorClass m c 0 ∪ colorClass m c 1 = colorClass m c 0 ∆ colorClass m c 1 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h0, h1]
    simp
  · rw [rowClass_one]
    have hd := colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide)
    have hu : colorClass m c 2 ∪ colorClass m c 3 = colorClass m c 2 ∆ colorClass m c 3 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h2, h3]
    simp


theorem rightPattern_rowBoundaries {ends : ι → Sym2 W} {m : Finset ι} {A B : Finset W}
    {u v : W} {c : ↑m → Fin 4} (h : RightPattern ends m A B u v c) :
    Sharpness.RandomCurrent.sources ends (rowClass m c 0) = A ∆ B ∧
      Sharpness.RandomCurrent.sources ends (rowClass m c 1) = ∅ := by
  rcases h with ⟨h0, h1, h2, h3, -⟩
  constructor
  · rw [rowClass_zero]
    have hd := colorClass_disjoint m c (show (0 : Fin 4) ≠ 1 by decide)
    have hu : colorClass m c 0 ∪ colorClass m c 1 = colorClass m c 0 ∆ colorClass m c 1 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h0, h1]
  · rw [rowClass_one]
    have hd := colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide)
    have hu : colorClass m c 2 ∪ colorClass m c 3 = colorClass m c 2 ∆ colorClass m c 3 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h2, h3, symmDiff_self]
    rfl

end FourColor
end GrahamGHS
end StatMech
