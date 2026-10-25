/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part8
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheIESlotFactor_eq_parts
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1)))
    (hST : S ⊆ sixVertexBetheWordMLSet w) (i : Fin (n + 1)) :
    (if i ∈ w then sixVertexBetheIELowerCoefficient c z S i
      else sixVertexBetheIEUpperCoefficient c z S i) =
      sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIEPrevLPart c z w S i := by
  by_cases hi : i ∈ w
  · have hiS : i ∉ S := by
      intro hiS
      exact ((mem_sixVertexBetheWordMLSet w i).mp (hST hiS)).1 hi
    simp [sixVertexBetheIELowerCoefficient, sixVertexBetheIEMPart,
      sixVertexBetheIEPrevLPart, hi, hiS]
  · have hpred : (finRotate (n + 1)).symm i ∉ S := by
      intro hpred
      have hml := (mem_sixVertexBetheWordMLSet w _).mp (hST hpred)
      exact hi (by simpa using hml.2)
    have hpred' : i - 1 ∉ S := by simpa using hpred
    simp [sixVertexBetheIEUpperCoefficient, sixVertexBetheIEMPart,
      sixVertexBetheIEPrevLPart, hi, hpred']

theorem sixVertexBetheIEPrevLPart_prod_eq_next
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1))) :
    (∏ i, sixVertexBetheIEPrevLPart c z w S i) =
      ∏ i, sixVertexBetheIENextLPart c z w S i := by
  calc
    (∏ i, sixVertexBetheIEPrevLPart c z w S i) =
        ∏ i, sixVertexBetheIEPrevLPart c z w S
          (finRotate (n + 1) i) :=
      (Equiv.prod_comp (finRotate (n + 1))
        (sixVertexBetheIEPrevLPart c z w S)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      unfold sixVertexBetheIEPrevLPart sixVertexBetheIENextLPart
      simp

theorem sixVertexBetheIEEdgeFactor_eq_base
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1)))
    (hST : S ⊆ sixVertexBetheWordMLSet w) (i : Fin (n + 1)) :
    sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIENextLPart c z w S i =
      if i ∈ S then 1 else sixVertexBetheWordEdgeBase c z w i := by
  by_cases hiS : i ∈ S
  · have hml := (mem_sixVertexBetheWordMLSet w i).mp (hST hiS)
    have hn' : i + 1 ∈ w := by simpa using hml.2
    simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
      hiS, hml.1, hn']
  · by_cases hi : i ∈ w
    · by_cases hn : finRotate (n + 1) i ∈ w
      · have hn' : i + 1 ∈ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']
      · have hn' : i + 1 ∉ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']
    · by_cases hn : finRotate (n + 1) i ∈ w
      · have hn' : i + 1 ∈ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']
      · have hn' : i + 1 ∉ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']

theorem sixVertexBetheIESlotProduct_eq_edgeBase
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1)))
    (hST : S ⊆ sixVertexBetheWordMLSet w) :
    ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
      ∏ i ∈ (Finset.univ \ w), sixVertexBetheIEUpperCoefficient c z S i) =
      ∏ i, if i ∈ S then 1 else sixVertexBetheWordEdgeBase c z w i := by
  calc
    ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w), sixVertexBetheIEUpperCoefficient c z S i) =
      ∏ i, if i ∈ w then sixVertexBetheIELowerCoefficient c z S i
        else sixVertexBetheIEUpperCoefficient c z S i := by
          rw [Finset.prod_ite]
          congr 2 <;> ext i <;> simp
    _ =
      ∏ i, (sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIEPrevLPart c z w S i) := by
          apply Finset.prod_congr rfl
          intro i _
          exact sixVertexBetheIESlotFactor_eq_parts c z w S hST i
    _ = (∏ i, sixVertexBetheIEMPart c z w S i) *
        ∏ i, sixVertexBetheIEPrevLPart c z w S i :=
      Finset.prod_mul_distrib
        (f := sixVertexBetheIEMPart c z w S)
        (g := sixVertexBetheIEPrevLPart c z w S)
    _ = (∏ i, sixVertexBetheIEMPart c z w S i) *
        ∏ i, sixVertexBetheIENextLPart c z w S i := by
      rw [sixVertexBetheIEPrevLPart_prod_eq_next]
    _ = ∏ i, (sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIENextLPart c z w S i) :=
      Finset.prod_mul_distrib.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact sixVertexBetheIEEdgeFactor_eq_base c z w S hST i

theorem sixVertexBetheIESlotProduct_eq_zero_of_not_subset
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1))) (hS : SixVertexBetheNoAdjacent S)
    (hnot : ¬ S ⊆ sixVertexBetheWordMLSet w) :
    ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
      ∏ i ∈ (Finset.univ \ w),
        sixVertexBetheIEUpperCoefficient c z S i) = 0 := by
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnot
  by_cases hiw : i ∈ w
  · have hpred : (finRotate (n + 1)).symm i ∉ S := by
      intro hpred
      apply hS ((finRotate (n + 1)).symm i) hpred
      simpa using hiS
    have hpred' : i - 1 ∉ S := by simpa using hpred
    have hzero : sixVertexBetheIELowerCoefficient c z S i = 0 := by
      simp [sixVertexBetheIELowerCoefficient, hiS, hpred']
    rw [Finset.prod_eq_zero hiw hzero, zero_mul]
  · have hnext : finRotate (n + 1) i ∉ w := by
      intro hnext
      exact hiT ((mem_sixVertexBetheWordMLSet w i).mpr ⟨hiw, hnext⟩)
    let j := finRotate (n + 1) i
    have hnext' : i + 1 ∉ w := by simpa using hnext
    have hjcomp : j ∈ (Finset.univ \ w) := by
      simp [j, hnext']
    have hjS : j ∉ S := hS i hiS
    have hpred : (finRotate (n + 1)).symm j ∈ S := by
      simpa [j] using hiS
    have hpred' : j - 1 ∈ S := by simpa using hpred
    have hzero : sixVertexBetheIEUpperCoefficient c z S j = 0 := by
      simp [sixVertexBetheIEUpperCoefficient, hjS, hpred']
    rw [Finset.prod_eq_zero hjcomp hzero, mul_zero]


theorem sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w : Finset (Fin (n + 1))) :
    sixVertexBetheRawIEWordCoefficient c z w =
      sixVertexBetheWordCoefficient c z (Equiv.refl _) w := by
  classical
  let T := sixVertexBetheWordMLSet w
  let P := (Finset.univ : Finset (Fin (n + 1))).powerset
  let Q := P.filter SixVertexBetheNoAdjacent
  have hTno : SixVertexBetheNoAdjacent T :=
    sixVertexBetheWordMLSet_noAdjacent w
  have hTPQ : T.powerset ⊆ Q := by
    intro S hS
    have hST : S ⊆ T := Finset.mem_powerset.mp hS
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.Subset.trans hST (Finset.subset_univ _))
    · intro i hiS hinext
      exact hTno i (hST hiS) (hST hinext)
  unfold sixVertexBetheRawIEWordCoefficient
  change (∑ S ∈ Q, (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i)) = _
  calc
    (∑ S ∈ Q, (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i)) =
      ∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i) := by
      symm
      apply Finset.sum_subset hTPQ
      intro S hSQ hST
      have hno : SixVertexBetheNoAdjacent S :=
        (Finset.mem_filter.mp hSQ).2
      have hnsub : ¬ S ⊆ T := by
        intro hsub
        exact hST (Finset.mem_powerset.mpr hsub)
      rw [sixVertexBetheIESlotProduct_eq_zero_of_not_subset
        c z w S hno hnsub, mul_zero]
    _ = ∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
        ∏ i, if i ∈ S then 1 else sixVertexBetheWordEdgeBase c z w i := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [sixVertexBetheIESlotProduct_eq_edgeBase]
      exact Finset.mem_powerset.mp hS
    _ = ∏ i, if i ∈ T then sixVertexBetheWordEdgeBase c z w i - 1
        else sixVertexBetheWordEdgeBase c z w i :=
      sum_powerset_neg_one_mul_complement_prod T
        (sixVertexBetheWordEdgeBase c z w)
    _ = _ := by
      rw [sixVertexBetheWordCoefficient_eq_edgeBase_sub]

theorem sixVertexBetheWordMonomial_refl_eq_endpoints
    {n : Nat} (N : Nat) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (w : Finset (Fin (n + 1))) :
    sixVertexBetheWordMonomial N z (Equiv.refl _) x w =
      ((∏ i ∈ w, z i ^ (sixVertexBetheShiftCoordinates N x i)) *
        ∏ i ∈ (Finset.univ \ w), z i ^ x i) := by
  unfold sixVertexBetheWordMonomial
  rw [Finset.prod_ite]
  congr 2 <;> ext i <;> simp


theorem sixVertexBetheCollisionFreeIntervalSum_eq_words
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, z i ≠ 1) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ w : Finset (Fin (n + 1)),
        sixVertexBetheWordCoefficient c z (Equiv.refl _) w *
          sixVertexBetheWordMonomial N z (Equiv.refl _) x w := by
  rw [sixVertexBetheCollisionFreeIntervalSum_eq_rawWords
    N c z x hgap hz0 hz1, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro w _
  rw [sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient,
    sixVertexBetheWordMonomial_refl_eq_endpoints]

theorem sixVertexBetheCollisionFreeTuple_strictMono
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) :
    StrictMono q := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  let a : Fin (n + 1) := i.castSucc
  let b : Fin (n + 1) := i.succ
  have hab : finRotate (n + 1) a = b := by
    apply Fin.ext
    simp [a, b]
  have hqa := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq a
  have hqb := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq b
  have hshift : sixVertexBetheShiftCoordinates N
      (sixVertexSectorIntCoordinates x) b =
      sixVertexSectorIntCoordinates x a := by
    simp [a, b, sixVertexBetheShiftCoordinates]
  have hle : q a ≤ q b := hqa.2.trans (hshift ▸ hqb.1)
  apply lt_of_le_of_ne hle
  intro heq
  have hqa_eq : q a = sixVertexSectorIntCoordinates x a :=
    le_antisymm hqa.2 ((hshift ▸ hqb.1).trans heq.ge)
  have hqb_eq : q b = sixVertexBetheShiftCoordinates N
      (sixVertexSectorIntCoordinates x) b :=
    le_antisymm (heq.ge.trans (hshift ▸ hqa.2)) hqb.1
  have hmem : a ∈ sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q := by
    rw [mem_sixVertexBetheCollisionSet]
    exact ⟨hqa_eq, by simpa [hab] using hqb_eq⟩
  rw [hfree] at hmem
  simp at hmem

theorem sixVertexBetheCollisionFreeTuple_wrap_lt
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) :
    q (Fin.last n) < q 0 + N := by
  have hlast := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq
    (Fin.last n)
  have hzero := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq 0
  have hle : q (Fin.last n) ≤ q 0 + N := by
    have ha : sixVertexSectorIntCoordinates x (Fin.last n) - N ≤ q 0 := by
      simpa [sixVertexBetheShiftCoordinates] using hzero.1
    omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hlast_eq : q (Fin.last n) = sixVertexSectorIntCoordinates x
        (Fin.last n) := by
      have ha : sixVertexSectorIntCoordinates x (Fin.last n) - N ≤ q 0 := by
        simpa [sixVertexBetheShiftCoordinates] using hzero.1
      apply le_antisymm hlast.2
      omega
    have hzero_eq : q 0 = sixVertexBetheShiftCoordinates N
        (sixVertexSectorIntCoordinates x) 0 := by
      apply le_antisymm
      · have := hlast.2
        simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
        omega
      · exact hzero.1
    have hmem : Fin.last n ∈ sixVertexBetheCollisionSet N
        (sixVertexSectorIntCoordinates x) q := by
      rw [mem_sixVertexBetheCollisionSet]
      constructor
      · exact hlast_eq
      · simpa [sixVertexBetheShiftCoordinates] using hzero_eq
    rw [hfree] at hmem
    simp at hmem

theorem sixVertexBetheTuple_nonnegative
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x)) (hq0 : 0 ≤ q 0) :
    ∀ i, 0 ≤ q i := by
  intro i
  induction i using Fin.cases with
  | zero => exact hq0
  | succ i =>
      have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
      have hx : 0 ≤ sixVertexSectorIntCoordinates x i.castSucc := by
        simp [sixVertexSectorIntCoordinates]
      simpa [sixVertexBetheShiftCoordinates] using hx.trans hi.1


end
end StatMech.FrontierD
