/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


theorem rightMaskCycleTranslate_trans
    (m : Finset I) (a b c q : ↑m -> Fin 4) :
    rightMaskCycleTranslate m b c
        (rightMaskCycleTranslate m a b q) =
      rightMaskCycleTranslate m a c q := by
  rw [rightMaskCycleTranslate, rightMaskCycleTranslate,
    rightMaskCycleTranslate, balancedSwap_comp_eq_symmDiff]
  simp only [balancedMiddleDifference, balancedOuterDifference]
  have hmiddle :
      (colorClass m a 1 ∆ colorClass m b 1) ∆
          (colorClass m b 1 ∆ colorClass m c 1) =
        colorClass m a 1 ∆ colorClass m c 1 := by
    calc
      _ = colorClass m a 1 ∆
          (colorClass m b 1 ∆ colorClass m b 1) ∆
            colorClass m c 1 := by ac_rfl
      _ = _ := by simp
  have houter :
      (colorClass m a 0 ∆ colorClass m b 0) ∆
          (colorClass m b 0 ∆ colorClass m c 0) =
        colorClass m a 0 ∆ colorClass m c 0 := by
    calc
      _ = colorClass m a 0 ∆
          (colorClass m b 0 ∆ colorClass m b 0) ∆
            colorClass m c 0 := by ac_rfl
      _ = _ := by simp
  rw [hmiddle, houter]


@[simp] theorem rightMaskCycleTranslate_self
    (m : Finset I) (a q : ↑m -> Fin 4) :
    rightMaskCycleTranslate m a a q = q := by
  rw [rightMaskCycleTranslate, balancedMiddleDifference,
    balancedOuterDifference, symmDiff_self, symmDiff_self]
  funext i
  simp [balancedSwap, middleSwapOn, outerSwapOn]


theorem rightMaskCycleTranslate_left_injective
    (m : Finset I) (a q : ↑m -> Fin 4)
    (ha : fourColorMaskProfile m a = fourColorMaskProfile m q) :
    Function.Injective (fun c :
      {c : ↑m -> Fin 4 // fourColorMaskProfile m c =
        fourColorMaskProfile m a} =>
      rightMaskCycleTranslate m a c.1 q) := by
  intro c d hcd
  apply Subtype.ext
  by_contra hcne
  have hprofileAC : fourColorMaskProfile m a =
      fourColorMaskProfile m c.1 := c.2.symm
  have hprofileCD : fourColorMaskProfile m c.1 =
      fourColorMaskProfile m d.1 := c.2.trans d.2.symm
  have hprofileCQ : fourColorMaskProfile m c.1 =
      fourColorMaskProfile m q := hprofileAC.symm.trans ha
  have hfixed : rightMaskCycleTranslate m c.1 d.1 q = q := by
    have hcongr := congrArg
      (rightMaskCycleTranslate m a c.1) hcd
    have hleft : rightMaskCycleTranslate m a c.1
        (rightMaskCycleTranslate m a c.1 q) = q := by
      rw [rightMaskCycleTranslate_comm m a c.1 q,
        rightMaskCycleTranslate_trans, rightMaskCycleTranslate_self]
    have hright : rightMaskCycleTranslate m a c.1
        (rightMaskCycleTranslate m a d.1 q) =
          rightMaskCycleTranslate m c.1 d.1 q := by
      rw [rightMaskCycleTranslate_comm m a d.1 q,
        rightMaskCycleTranslate_trans,
        rightMaskCycleTranslate_comm m d.1 c.1 q]
    rw [hleft, hright] at hcongr
    exact hcongr.symm
  exact (rightMaskCycleTranslate_ne m c.1 d.1 q
    (congrArg Prod.fst hprofileCD)
    (congrArg Prod.snd hprofileCD)
    (congrArg Prod.fst hprofileCQ)
    (congrArg Prod.snd hprofileCQ) hcne) hfixed


theorem rightMaskCycleTranslate_rows
    (m : Finset I) (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q) :
    rowClass m (rightMaskCycleTranslate m a c q) 0 =
        rowClass m q 0 ∆ rightMaskCycleDifference m a c ∧
      rowClass m (rightMaskCycleTranslate m a c q) 1 =
        rowClass m q 1 ∆ rightMaskCycleDifference m a c := by
  have hX : balancedMiddleDifference m a c ⊆
      colorClass m q 1 ∪ colorClass m q 2 := by
    have hsub := balancedMiddleDifference_subset m a c
      (congrArg Prod.fst hac)
    have hmid : middleMask m a = middleMask m q :=
      congrArg Prod.fst haq
    rw [← middleMask, ← hmid]
    exact hsub
  have hY : balancedOuterDifference m a c ⊆
      colorClass m q 0 ∪ colorClass m q 3 := by
    have hsub := balancedOuterDifference_subset m a c
      (congrArg Prod.snd hac)
    have hout : outerMask m a = outerMask m q :=
      congrArg Prod.snd haq
    rw [← outerMask, ← hout]
    exact hsub
  constructor
  · exact rowClass_balancedSwap_zero hX hY
  · exact rowClass_balancedSwap_one hX hY


theorem not_conn_symmDiff_of_noCrossing_componentComplement
    (ends : I -> Sym2 W) (K D : Finset I) (k zero : W)
    (hdisc : ¬ connK ends K k zero)
    (hcross : NoCrossingK ends (K ∆ D)
      (StatMech.FrontierA.grahamComponentComplement ends K k)) :
    ¬ connK ends (K ∆ D) k zero := by
  intro hconn
  have hk : k ∉ StatMech.FrontierA.grahamComponentComplement ends K k :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends K k
  have hzero : zero ∈
      StatMech.FrontierA.grahamComponentComplement ends K k := by
    rw [StatMech.FrontierA.grahamComponentComplement, mem_notConnCompK]
    exact hdisc
  exact (connK_not_mem_of_noCrossing hcross hk hconn) hzero


theorem exists_mem_difference_crossing_of_toggle_connected
    (ends : I -> Sym2 W) (K D : Finset I) (k zero : W)
    (hdisc : ¬ connK ends K k zero)
    (hconn : connK ends (K ∆ D) k zero) :
    ∃ e ∈ D, CrossesRootComponentCut ends K k e := by
  let S := StatMech.FrontierA.grahamComponentComplement ends K k
  have hk : k ∉ S :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends K k
  have hzero : zero ∈ S := by
    dsimp only [S]
    rw [StatMech.FrontierA.grahamComponentComplement, mem_notConnCompK]
    exact hdisc
  obtain ⟨e, he, hcross⟩ := exists_crossing_edge_mem_sdiff_of_connK
    (StatMech.FrontierA.grahamComponentComplement_noCrossing ends K k)
      hk hzero hconn
  have he' := Finset.mem_sdiff.mp he
  have heD : e ∈ D := by
    rcases Finset.mem_symmDiff.mp he'.1 with heK | heD
    · exact False.elim (he'.2 heK.1)
    · exact heD.1
  exact ⟨e, heD, hcross⟩


theorem exists_cycleDifference_crossing_of_translate_not_disconnects
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
    (hq : RowsDisconnect ends m q k zero)
    (hfail : ¬ RowsDisconnect ends m
      (rightMaskCycleTranslate m a c q) k zero) :
    (∃ e ∈ rightMaskCycleDifference m a c,
        CrossesRootComponentCut ends (rowClass m q 0) k e) ∨
      ∃ e ∈ rightMaskCycleDifference m a c,
        CrossesRootComponentCut ends (rowClass m q 1) k e := by
  have hrows := rightMaskCycleTranslate_rows m a c q hac haq
  rw [RowsDisconnect] at hq hfail
  have hconn :
      connK ends (rowClass m q 0 ∆ rightMaskCycleDifference m a c)
          k zero ∨
        connK ends (rowClass m q 1 ∆ rightMaskCycleDifference m a c)
          k zero := by
    rw [hrows.1, hrows.2] at hfail
    tauto
  rcases hconn with hconn | hconn
  · exact Or.inl (exists_mem_difference_crossing_of_toggle_connected
      ends (rowClass m q 0) (rightMaskCycleDifference m a c)
        k zero hq.1 hconn)
  · exact Or.inr (exists_mem_difference_crossing_of_toggle_connected
      ends (rowClass m q 1) (rightMaskCycleDifference m a c)
        k zero hq.2 hconn)


theorem rightMaskCycleTranslate_disconnects_of_no_crossing_edges
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
    (hq : RowsDisconnect ends m q k zero)
    (hno0 : ∀ e ∈ rightMaskCycleDifference m a c,
      ¬ CrossesRootComponentCut ends (rowClass m q 0) k e)
    (hno1 : ∀ e ∈ rightMaskCycleDifference m a c,
      ¬ CrossesRootComponentCut ends (rowClass m q 1) k e) :
    RowsDisconnect ends m
      (rightMaskCycleTranslate m a c q) k zero := by
  by_contra hfail
  rcases exists_cycleDifference_crossing_of_translate_not_disconnects
      ends m k zero a c q hac haq hq hfail with hcross | hcross
  · obtain ⟨e, he, hcut⟩ := hcross
    exact hno0 e he hcut
  · obtain ⟨e, he, hcut⟩ := hcross
    exact hno1 e he hcut


end StatMech.GrahamGHS.FourColor
