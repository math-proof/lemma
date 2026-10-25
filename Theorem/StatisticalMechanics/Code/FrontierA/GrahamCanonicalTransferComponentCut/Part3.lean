/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rootSpanning_union_of_everyEdgeComponentMeets
    (ends : I -> Sym2 W) (E D : Finset I) (u : W)
    (hE : RootSpanning ends E u)
    (hmeet : EveryEdgeComponentMeets ends D E) :
    RootSpanning ends (E ∪ D) u := by
  classical
  apply rootSpanning_union_of_edgeComponents_meet ends E D u hE
  intro i hiD x hx
  obtain ⟨e, he⟩ := hmeet i hiD
  have he' := Finset.mem_inter.mp he
  have heComp : e ∈ edgeComponent ends D (ends i).out.1 := he'.1
  have heE : e ∈ E := he'.2
  let r := (ends i).out.1
  have hr : r ∈ ends i := Sym2.out_fst_mem (ends i)
  have hiComp : i ∈ edgeComponent ends D r :=
    mem_edgeComponent_of_endpoint hiD hr
  have hrx : connK ends D r x := by
    rw [edgeComponent, Finset.mem_filter] at hiComp
    exact hiComp.2 x hx
  obtain ⟨⟨a, b⟩, hab⟩ := (ends e).exists_rep
  have ha : a ∈ ends e := hab ▸ Sym2.mem_mk_left a b
  have hry : connK ends D r a := by
    rw [edgeComponent, Finset.mem_filter] at heComp
    exact heComp.2 a ha
  exact ⟨e, Finset.mem_inter.mpr ⟨
    (by
      rw [edgeComponent, Finset.mem_filter] at heComp
      exact heComp.1), heE⟩,
    a, ha, (connK_symm ends D hrx).trans hry⟩


theorem subset_edgeComponent_of_subset_of_everyEdgeComponentMeets
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K)
    (hmeet : EveryEdgeComponentMeets ends D
      (edgeComponent ends K u)) :
    D ⊆ edgeComponent ends K u := by
  apply subset_edgeComponent_of_subset_of_rootSpanning_union
    ends K D u hDK
  exact rootSpanning_union_of_everyEdgeComponentMeets ends
    (edgeComponent ends K u) D u
      (edgeComponent_rootSpanning ends K u) hmeet


theorem everyEdgeComponentMeets_edgeComponent_iff_subset
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K) :
    EveryEdgeComponentMeets ends D (edgeComponent ends K u) ↔
      D ⊆ edgeComponent ends K u := by
  classical
  constructor
  · exact subset_edgeComponent_of_subset_of_everyEdgeComponentMeets
      ends K D u hDK
  · intro hD i hiD
    refine ⟨i, Finset.mem_inter.mpr ⟨?_, hD hiD⟩⟩
    exact mem_edgeComponent_of_endpoint hiD
      (Sym2.out_fst_mem (ends i))


theorem mem_canonicalNormalRow_iff
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I) :
    i ∈ canonicalNormalRow ends m k zero c ↔
      (i ∈ rowClass m c 0 ∧
          i ∉ canonicalTransferUnion ends m k zero c) ∨
        (i ∈ canonicalTransferUnion ends m k zero c ∧
          i ∉ rowClass m c 0) := by
  classical
  simp only [canonicalNormalRow, Finset.mem_symmDiff]


theorem canonicalNormalRow_eq_rowClass_selfSwap
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    canonicalNormalRow ends m k zero c =
      rowClass m
        (balancedSwap m
          (canonicalMiddleTransfer ends m c k zero)
          (canonicalOuterTransfer ends m c k zero) c) 0 := by
  have hv := canonicalTransfers_valid hloop hjk hkl hc
  rw [canonicalNormalRow,
    rowClass_balancedSwap_zero hv.1 hv.2.1,
    canonicalTransferUnion]


theorem canonicalNormalRow_no_incident_zero
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    ∀ i ∈ canonicalNormalRow ends m k zero c, zero ∉ ends i := by
  let d := balancedSwap m
    (canonicalMiddleTransfer ends m c k zero)
    (canonicalOuterTransfer ends m c k zero) c
  have hrows := canonicalBalancedSwap_rows hloop hjk hkl hc
  rw [canonicalNormalRow_eq_rowClass_selfSwap hloop hjk hkl hc,
    hrows.1]
  exact exchangeFirstRow_no_incident_zero hc.2.2.2.2.2


theorem mem_canonicalNormalRow_of_mem_k
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c)
    {i : I} (him : i ∈ m) (hik : k ∈ ends i) :
    i ∈ canonicalNormalRow ends m k zero c := by
  let d := balancedSwap m
    (canonicalMiddleTransfer ends m c k zero)
    (canonicalOuterTransfer ends m c k zero) c
  have hrows := canonicalBalancedSwap_rows hloop hjk hkl hc
  have hnotSecond : i ∉ rowClass m d 1 := by
    rw [hrows.2]
    intro hiSecond
    exact exchangeSecondRow_no_incident_k hc.2.2.2.2.1
      i hiSecond hik
  rw [canonicalNormalRow_eq_rowClass_selfSwap hloop hjk hkl hc]
  rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hnotSecond
  exact Classical.byContradiction fun hi => hnotSecond ⟨him, hi⟩

theorem union_pair_symmDiff_eq_union_symmDiff
    {A B C D M O : Finset I}
    (hAM : A ⊆ M) (hBM : B ⊆ M)
    (hCO : C ⊆ O) (hDO : D ⊆ O)
    (hMO : Disjoint M O) :
    (A ∆ B) ∪ (C ∆ D) = (A ∪ C) ∆ (B ∪ D) := by
  classical
  ext i
  have hAC : i ∈ A -> i ∈ C -> False := fun hiA hiC =>
    (Finset.disjoint_left.mp hMO) (hAM hiA) (hCO hiC)
  have hAD : i ∈ A -> i ∈ D -> False := fun hiA hiD =>
    (Finset.disjoint_left.mp hMO) (hAM hiA) (hDO hiD)
  have hBC : i ∈ B -> i ∈ C -> False := fun hiB hiC =>
    (Finset.disjoint_left.mp hMO) (hBM hiB) (hCO hiC)
  have hBD : i ∈ B -> i ∈ D -> False := fun hiB hiD =>
    (Finset.disjoint_left.mp hMO) (hBM hiB) (hDO hiD)
  simp only [Finset.mem_union, Finset.mem_symmDiff]
  tauto

theorem sdiff_symmDiff_symmDiff
    {A B C m : Finset I} (hA : A ⊆ m) (hB : B ⊆ m) (hC : C ⊆ m) :
    m \ (A ∆ B ∆ C) = (m \ A) ∆ B ∆ C := by
  classical
  ext i
  by_cases him : i ∈ m
  · by_cases hiA : i ∈ A <;>
      by_cases hiB : i ∈ B <;>
      by_cases hiC : i ∈ C <;>
      simp [Finset.mem_sdiff, Finset.mem_symmDiff,
        him, hiA, hiB, hiC]
  · have hiA : i ∉ A := fun hi => him (hA hi)
    have hiB : i ∉ B := fun hi => him (hB hi)
    have hiC : i ∉ C := fun hi => him (hC hi)
    simp [Finset.mem_sdiff, Finset.mem_symmDiff,
      him, hiA, hiB, hiC]


theorem rowClass_canonicalQuadrangleCompletion_zero
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 0 =
      rowClass m c.1.1 0 ∆
        canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  let Xa := canonicalMiddleTransfer ends m a.1.1 k zero
  let Xb := canonicalMiddleTransfer ends m b.1.1 k zero
  let Ya := canonicalOuterTransfer ends m a.1.1 k zero
  let Yb := canonicalOuterTransfer ends m b.1.1 k zero
  have hva := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  have hvb := canonicalTransfers_valid_on_sameMask hloop hjk hkl b c
  have hX : Xa ∆ Xb ⊆ colorClass m c.1.1 1 ∪
      colorClass m c.1.1 2 := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with hi | hi
    · exact hva.1 hi.1
    · exact hvb.1 hi.1
  have hY : Ya ∆ Yb ⊆ colorClass m c.1.1 0 ∪
      colorClass m c.1.1 3 := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with hi | hi
    · exact hva.2.1 hi.1
    · exact hvb.2.1 hi.1
  have hunion : (Xa ∆ Xb) ∪ (Ya ∆ Yb) =
      (Xa ∪ Ya) ∆ (Xb ∪ Yb) :=
    union_pair_symmDiff_eq_union_symmDiff
      (by simpa only [Xa, middleMask] using hva.1)
      (by simpa only [Xb, middleMask] using hvb.1)
      (by simpa only [Ya, outerMask] using hva.2.1)
      (by simpa only [Yb, outerMask] using hvb.2.1)
      (middleMask_disjoint_outerMask m c.1.1)
  rw [canonicalQuadrangleCompletion]
  change rowClass m (balancedSwap m (Xa ∆ Xb) (Ya ∆ Yb) c.1.1) 0 = _
  rw [rowClass_balancedSwap_zero hX hY]
  rw [hunion]
  dsimp only [canonicalTransferUnion, Xa, Xb, Ya, Yb]
  rw [symmDiff_assoc]


theorem rowClass_canonicalQuadrangleCompletion_one
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 1 =
      rowClass m c.1.1 1 ∆
        canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  classical
  have hTa : canonicalTransferUnion ends m k zero a.1.1 ⊆ m :=
    canonicalTransferUnion_subset_m
    hloop hjk hkl a
  have hTb : canonicalTransferUnion ends m k zero b.1.1 ⊆ m :=
    canonicalTransferUnion_subset_m
    hloop hjk hkl b
  have hzero := rowClass_canonicalQuadrangleCompletion_zero
    hloop hjk hkl a b c
  rw [rowClass_one_eq_sdiff, hzero, rowClass_one_eq_sdiff]
  apply sdiff_symmDiff_symmDiff
  · intro i hi
    rw [rowClass_zero] at hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact colorClass_subset m c.1.1 0 hi
    · exact colorClass_subset m c.1.1 1 hi
  · exact hTa
  · exact hTb


theorem rowClass_canonicalQuadrangleCompletion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) (rho : Fin 2) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) rho =
      rowClass m c.1.1 rho ∆
        canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  fin_cases rho
  · exact rowClass_canonicalQuadrangleCompletion_zero
      hloop hjk hkl a b c
  · exact rowClass_canonicalQuadrangleCompletion_one
      hloop hjk hkl a b c


theorem canonicalTranslatedRow_quadrangleCompletion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) := by
  classical
  unfold canonicalTranslatedRow
  rw [rowClass_canonicalQuadrangleCompletion_zero
    hloop hjk hkl a b c]
  exact (symmDiff_symmDiff_cancel_right
    (canonicalTransferUnion ends m k zero b.1.1)
    (rowClass m c.1.1 0 ∆
      canonicalTransferUnion ends m k zero a.1.1)).symm

theorem mem_iff_mem_symmDiff_of_not_mem_threefold
    (C A B : Finset I) (i : I) (hi : i ∉ C ∆ A ∆ B) :
    (i ∈ C ↔ i ∈ A ∆ B) := by
  classical
  simp only [Finset.mem_symmDiff] at hi ⊢
  tauto


theorem rowClass_pair_parity_of_not_mem_canonicalQuadrangleCompletion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) (rho : Fin 2)
    {i : I}
    (hi : i ∉ rowClass m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) rho) :
    (i ∈ rowClass m c.1.1 rho) ↔
      i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  have hrow := rowClass_canonicalQuadrangleCompletion
    hloop hjk hkl a b c rho
  apply mem_iff_mem_symmDiff_of_not_mem_threefold
  rwa [← hrow]


theorem fourfold_symmDiff_subset_union
    (A B C D : Finset I) :
    A ∆ B ∆ C ∆ D ⊆ ((A ∪ B) ∪ C) ∪ D := by
  classical
  intro i hi
  simp only [Finset.mem_symmDiff, Finset.mem_union] at hi ⊢
  tauto


theorem exists_other_mem_of_mem_of_not_mem_fourfold
    (A B C D : Finset I) (i : I)
    (hiA : i ∈ A) (hnot : i ∉ A ∆ B ∆ C ∆ D) :
    i ∈ B ∨ i ∈ C ∨ i ∈ D := by
  classical
  by_contra hother
  have hiB : i ∉ B := fun hi => hother (Or.inl hi)
  have hiC : i ∉ C := fun hi => hother (Or.inr (Or.inl hi))
  have hiD : i ∉ D := fun hi => hother (Or.inr (Or.inr hi))
  apply hnot
  simp [Finset.mem_symmDiff, hiA, hiB, hiC, hiD]


end StatMech.GrahamGHS.FourColor
