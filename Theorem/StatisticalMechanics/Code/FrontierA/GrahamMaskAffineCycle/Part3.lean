/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part2
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem leftMaskCycleEmbedding_surjective_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    Function.Surjective
      (leftMaskCycleEmbedding ends m j k l zero p) := by
  apply embedding_surjective_of_card_le_two_of_ne
    (leftMaskCycleEmbedding ends m j k l zero p) c d hcd
  simpa only [Fintype.card_prod] using hcycle


theorem exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    ∃ e : leftMaskFiber ends m j k l zero p,
      leftMaskCyclePair ends m j k l zero p e =
        emptyMaskCyclePair ends p :=
  leftMaskCycleEmbedding_surjective_of_cycleProduct_le_two
    ends m j k l zero p c d hcd hcycle (emptyMaskCyclePair ends p)


theorem cycleProduct_le_two_factor_card_eq_one
    (ends : I → Sym2 W) (p : Finset I × Finset I)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    Fintype.card (boundarySector ends p.1 ∅) = 1 ∨
      Fintype.card (boundarySector ends p.2 ∅) = 1 := by
  have hpos1 : 0 < Fintype.card (boundarySector ends p.1 ∅) :=
    Fintype.card_pos_iff.mpr ⟨emptyBoundarySector ends p.1⟩
  have hpos2 : 0 < Fintype.card (boundarySector ends p.2 ∅) :=
    Fintype.card_pos_iff.mpr ⟨emptyBoundarySector ends p.2⟩
  by_contra h
  push Not at h
  have htwo1 : 2 ≤ Fintype.card (boundarySector ends p.1 ∅) := by omega
  have htwo2 : 2 ≤ Fintype.card (boundarySector ends p.2 ∅) := by omega
  nlinarith


theorem colorClass_zero_eq_outerMask_sdiff_three
    (m : Finset I) (c : ↑m → Fin 4) :
    colorClass m c 0 = outerMask m c \ colorClass m c 3 := by
  rw [outerMask]
  ext i
  have hd := Finset.disjoint_left.mp
    (colorClass_disjoint m c (show (0 : Fin 4) ≠ 3 by decide))
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop


theorem leftMaskCycleDifference_empty_side_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    balancedMiddleDifference m c.1.1 d.1.1 = ∅ ∨
      balancedOuterDifference m c.1.1 d.1.1 = ∅ := by
  rcases cycleProduct_le_two_factor_card_eq_one ends p hcycle with hmid | hout
  · left
    have hsub : Subsingleton (boundarySector ends p.1 ∅) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hp := hsub.elim
      (leftMaskCyclePair ends m j k l zero p c).1
      (leftMaskCyclePair ends m j k l zero p d).1
    have hone : colorClass m c.1.1 1 = colorClass m d.1.1 1 :=
      congrArg Subtype.val hp
    rw [balancedMiddleDifference, hone, symmDiff_self]
    rfl
  · right
    have hsub : Subsingleton (boundarySector ends p.2 ∅) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hp := hsub.elim
      (leftMaskCyclePair ends m j k l zero p c).2
      (leftMaskCyclePair ends m j k l zero p d).2
    have hthree : colorClass m c.1.1 3 = colorClass m d.1.1 3 :=
      congrArg Subtype.val hp
    have houter : outerMask m c.1.1 = outerMask m d.1.1 :=
      (congrArg Prod.snd c.2).trans (congrArg Prod.snd d.2).symm
    have hzero : colorClass m c.1.1 0 = colorClass m d.1.1 0 := by
      rw [colorClass_zero_eq_outerMask_sdiff_three,
        colorClass_zero_eq_outerMask_sdiff_three, houter, hthree]
    rw [balancedOuterDifference, hzero, symmDiff_self]
    rfl


theorem rows_eq_masks_of_leftMaskCyclePair_eq_empty
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p)
    (hc : leftMaskCyclePair ends m j k l zero p c =
      emptyMaskCyclePair ends p) :
    rowClass m c.1.1 0 = p.2 ∧ rowClass m c.1.1 1 = p.1 := by
  have hone : colorClass m c.1.1 1 = ∅ := by
    have h := congrArg (fun z => z.1.1) hc
    simpa [leftMaskCyclePair, emptyMaskCyclePair,
      emptyBoundarySector] using h
  have hthree : colorClass m c.1.1 3 = ∅ := by
    have h := congrArg (fun z => z.2.1) hc
    simpa [leftMaskCyclePair, emptyMaskCyclePair,
      emptyBoundarySector] using h
  have hmid : middleMask m c.1.1 = p.1 := congrArg Prod.fst c.2
  have hout : outerMask m c.1.1 = p.2 := congrArg Prod.snd c.2
  constructor
  · calc
      rowClass m c.1.1 0 = colorClass m c.1.1 0 := by
        simp [rowClass_zero, hone]
      _ = outerMask m c.1.1 := by simp [outerMask, hthree]
      _ = p.2 := hout
  · calc
      rowClass m c.1.1 1 = colorClass m c.1.1 2 := by
        simp [rowClass_one, hthree]
      _ = middleMask m c.1.1 := by simp [middleMask, hone]
      _ = p.1 := hmid


theorem exists_leftMaskFiber_with_disconnected_masks_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    ∃ e : leftMaskFiber ends m j k l zero p,
      ¬ connK ends p.1 k zero ∧ ¬ connK ends p.2 k zero := by
  obtain ⟨e, he⟩ := exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two
    ends m j k l zero p c d hcd hcycle
  have hrows := rows_eq_masks_of_leftMaskCyclePair_eq_empty
    ends m j k l zero p e he
  refine ⟨e, ?_, ?_⟩
  · simpa [RowsDisconnect, hrows.2] using e.1.2.2.2.2.2.2
  · simpa [RowsDisconnect, hrows.1] using e.1.2.2.2.2.2.1


theorem rightPattern_of_sourceless_balancedSwap
    {ends : I → Sym2 W} {m X Y : Finset I}
    {A B : Finset W} {u v : W} {c : ↑m → Fin 4}
    (hright : RightPattern ends m A B u v c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
    (hsrcX : sources ends X = ∅)
    (hsrcY : sources ends Y = ∅)
    (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
    RightPattern ends m A B u v (balancedSwap m X Y c) := by
  rcases hright with ⟨h0, h1, h2, h3, -⟩
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


end StatMech.GrahamGHS.FourColor
