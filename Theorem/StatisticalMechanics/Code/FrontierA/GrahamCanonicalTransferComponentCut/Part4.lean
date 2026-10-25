/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem atLeastTwoOfFour_of_mem_union_of_not_mem_symmDiff
    (A B C D : Finset I) (i : I)
    (hi : i ∈ ((A ∪ B) ∪ C) ∪ D)
    (hnot : i ∉ A ∆ B ∆ C ∆ D) :
    AtLeastTwoOfFour A B C D i := by
  classical
  simp only [AtLeastTwoOfFour, Finset.mem_union,
    Finset.mem_symmDiff] at hi hnot ⊢
  tauto


theorem four_canonicalTransferUnion_twoRootSpanning
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c d : ↑m -> Fin 4) :
    TwoRootSpanning ends
      (((canonicalTransferUnion ends m k zero a ∪
          canonicalTransferUnion ends m k zero b) ∪
        canonicalTransferUnion ends m k zero c) ∪
        canonicalTransferUnion ends m k zero d) k zero := by
  exact twoRootSpanning_union
    (twoRootSpanning_union
      (twoRootSpanning_union
        (canonicalTransferUnion_twoRootSpanning ends m k zero a)
        (canonicalTransferUnion_twoRootSpanning ends m k zero b))
      (canonicalTransferUnion_twoRootSpanning ends m k zero c))
    (canonicalTransferUnion_twoRootSpanning ends m k zero d)


theorem exists_two_canonicalTransfers_at_failedCutCrossing
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hkzero : connK ends K k zero)
    (hD : canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y ⊆ K)
    {i : I}
    (hi : i ∈ (canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y) \
      edgeComponent ends K zero) :
    ∃ e,
      e ∈ (((canonicalTransferUnion ends m k zero r ∪
          canonicalTransferUnion ends m k zero s) ∪
        canonicalTransferUnion ends m k zero x) ∪
        canonicalTransferUnion ends m k zero y) \ K ∧
      (∃ a b, a ∈ ends e ∧ b ∈ ends e ∧
        a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧
        b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero) ∧
      AtLeastTwoOfFour
        (canonicalTransferUnion ends m k zero r)
        (canonicalTransferUnion ends m k zero s)
        (canonicalTransferUnion ends m k zero x)
        (canonicalTransferUnion ends m k zero y) e := by
  have hi' := Finset.mem_sdiff.mp hi
  have hiK : i ∈ K \ edgeComponent ends K zero :=
    Finset.mem_sdiff.mpr ⟨hD hi'.1, hi'.2⟩
  have hiUnion : i ∈
      ((canonicalTransferUnion ends m k zero r ∪
          canonicalTransferUnion ends m k zero s) ∪
        canonicalTransferUnion ends m k zero x) ∪
        canonicalTransferUnion ends m k zero y :=
    fourfold_symmDiff_subset_union
      (canonicalTransferUnion ends m k zero r)
      (canonicalTransferUnion ends m k zero s)
      (canonicalTransferUnion ends m k zero x)
      (canonicalTransferUnion ends m k zero y) hi'.1
  obtain ⟨e, he, hcut⟩ :=
    exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent
      ends K
        (((canonicalTransferUnion ends m k zero r ∪
            canonicalTransferUnion ends m k zero s) ∪
          canonicalTransferUnion ends m k zero x) ∪
          canonicalTransferUnion ends m k zero y)
        k zero hkzero
        (four_canonicalTransferUnion_twoRootSpanning
          ends m k zero r s x y)
        hiK hiUnion
  have he' := Finset.mem_sdiff.mp he
  have heNotD : e ∉ canonicalTransferUnion ends m k zero r ∆
      canonicalTransferUnion ends m k zero s ∆
      canonicalTransferUnion ends m k zero x ∆
      canonicalTransferUnion ends m k zero y :=
    fun heD => he'.2 (hD heD)
  exact ⟨e, he, hcut,
    atLeastTwoOfFour_of_mem_union_of_not_mem_symmDiff
      (canonicalTransferUnion ends m k zero r)
      (canonicalTransferUnion ends m k zero s)
      (canonicalTransferUnion ends m k zero x)
      (canonicalTransferUnion ends m k zero y)
      e he'.1 heNotD⟩


theorem exists_second_canonicalTransfer_at_failedCutCrossing
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hkzero : connK ends K k zero)
    (hD : canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y ⊆ K)
    {i : I} (hi : i ∈ K \ edgeComponent ends K zero)
    (hir : i ∈ canonicalTransferUnion ends m k zero r) :
    ∃ e,
      e ∈ canonicalTransferUnion ends m k zero r \ K ∧
      (∃ a b, a ∈ ends e ∧ b ∈ ends e ∧
        a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧
        b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero) ∧
      (e ∈ canonicalTransferUnion ends m k zero s ∨
        e ∈ canonicalTransferUnion ends m k zero x ∨
        e ∈ canonicalTransferUnion ends m k zero y) := by
  obtain ⟨e, he, hcut⟩ :=
    exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent
      ends K (canonicalTransferUnion ends m k zero r) k zero
        hkzero
        (canonicalTransferUnion_twoRootSpanning ends m k zero r)
        hi hir
  have he' := Finset.mem_sdiff.mp he
  have heNotD : e ∉ canonicalTransferUnion ends m k zero r ∆
      canonicalTransferUnion ends m k zero s ∆
      canonicalTransferUnion ends m k zero x ∆
      canonicalTransferUnion ends m k zero y := by
    intro heD
    exact he'.2 (hD heD)
  exact ⟨e, he, hcut,
    exists_other_mem_of_mem_of_not_mem_fourfold
      (canonicalTransferUnion ends m k zero r)
      (canonicalTransferUnion ends m k zero s)
      (canonicalTransferUnion ends m k zero x)
      (canonicalTransferUnion ends m k zero y)
      e he'.1 heNotD⟩


theorem canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y =
      canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y := by
  have hrow := rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq
    r s x y hxy
  unfold canonicalNormalRow
  calc
    (rowClass m x 0 ∆ canonicalTransferUnion ends m k zero x) ∆
          (rowClass m y 0 ∆ canonicalTransferUnion ends m k zero y) =
        (rowClass m x 0 ∆ rowClass m y 0) ∆
          (canonicalTransferUnion ends m k zero x ∆
            canonicalTransferUnion ends m k zero y) := by ac_rfl
    _ = (canonicalTransferUnion ends m k zero r ∆
          canonicalTransferUnion ends m k zero s) ∆
        (canonicalTransferUnion ends m k zero x ∆
          canonicalTransferUnion ends m k zero y) := by rw [hrow]
    _ = canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y := by ac_rfl


theorem canonicalNormalRow_symmDiff_eq_pairDifferences_of_translatedRow_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y =
      (canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero x) ∆
      (canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero y) := by
  rw [canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r s x y hxy]
  ac_rfl


theorem canonicalQuadrangleCompletion_normalRowDiscrepancy
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    canonicalNormalRow ends m k zero c.1.1 ∆
        canonicalNormalRow ends m k zero d =
      canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 ∆
        canonicalTransferUnion ends m k zero d := by
  dsimp only
  exact canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero a.1.1 b.1.1 c.1.1
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1)
      (canonicalTranslatedRow_quadrangleCompletion
        hloop hjk hkl a b c)

theorem mem_threefold_of_mem_fourfold_of_not_mem_fourth
    (A B C D : Finset I) {i : I}
    (hi : i ∈ A ∆ B ∆ C ∆ D) (hiD : i ∉ D) :
    i ∈ A ∆ B ∆ C := by
  classical
  simp only [Finset.mem_symmDiff] at hi ⊢
  tauto


theorem canonicalQuadrangleCompletion_nonrootRowZero_discrepancy_threeLabels
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    {i : I}
    (hiD : i ∈ canonicalNormalRow ends m k zero c.1.1 ∆
      canonicalNormalRow ends m k zero
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1))
    (hiK : i ∈ rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 0 \
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 0) zero) :
    i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
      canonicalTransferUnion ends m k zero b.1.1 ∆
      canonicalTransferUnion ends m k zero c.1.1 := by
  classical
  have hfour := hiD
  rw [canonicalQuadrangleCompletion_normalRowDiscrepancy
    hloop hjk hkl a b c] at hfour
  have hnot : i ∉ canonicalTransferUnion ends m k zero
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) := by
    intro hiT
    exact (Finset.disjoint_left.mp
      (canonicalTransferUnion_disjoint_nonrootRowZero
        ends m k zero
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1))) hiT hiK
  exact mem_threefold_of_mem_fourfold_of_not_mem_fourth
    _ _ _ _ hfour hnot


theorem canonicalQuadrangleCompletion_nonrootRowOne_discrepancy_threeLabels
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    {i : I}
    (hiD : i ∈ canonicalNormalRow ends m k zero c.1.1 ∆
      canonicalNormalRow ends m k zero
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1))
    (hiK : i ∈ rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 1 \
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k) :
    i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
      canonicalTransferUnion ends m k zero b.1.1 ∆
      canonicalTransferUnion ends m k zero c.1.1 := by
  classical
  have hfour := hiD
  rw [canonicalQuadrangleCompletion_normalRowDiscrepancy
    hloop hjk hkl a b c] at hfour
  have hnot : i ∉ canonicalTransferUnion ends m k zero
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) := by
    intro hiT
    exact (Finset.disjoint_left.mp
      (canonicalTransferUnion_disjoint_nonrootRowOne
        ends m k zero
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1))) hiT hiK
  exact mem_threefold_of_mem_fourfold_of_not_mem_fourth
    _ _ _ _ hfour hnot


theorem canonicalTransferPairDifference_eq_translatedRow_symmDiff_normalRow
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r x : ↑m -> Fin 4) :
    canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero x =
      canonicalTranslatedRow ends m k zero r x ∆
        canonicalNormalRow ends m k zero x := by
  unfold canonicalTranslatedRow canonicalNormalRow
  symm
  calc
    (rowClass m x 0 ∆ canonicalTransferUnion ends m k zero r) ∆
          (rowClass m x 0 ∆ canonicalTransferUnion ends m k zero x) =
        (rowClass m x 0 ∆ rowClass m x 0) ∆
          (canonicalTransferUnion ends m k zero r ∆
            canonicalTransferUnion ends m k zero x) := by ac_rfl
    _ = canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero x := by simp


theorem canonicalNormalRow_sdiff_eq_of_component_meets
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (K : Finset I) (x y : ↑m -> Fin 4)
    (hrow : canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y ⊆ K)
    (hmeet : EveryEdgeComponentMeets ends
      (canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y)
      (edgeComponent ends K zero)) :
    canonicalNormalRow ends m k zero x \
        edgeComponent ends K zero =
      canonicalNormalRow ends m k zero y \
        edgeComponent ends K zero := by
  have hcomponent : canonicalNormalRow ends m k zero x ∆
      canonicalNormalRow ends m k zero y ⊆
        edgeComponent ends K zero :=
    subset_edgeComponent_of_subset_of_everyEdgeComponentMeets
      ends K
        (canonicalNormalRow ends m k zero x ∆
          canonicalNormalRow ends m k zero y)
        zero hrow hmeet
  classical
  ext i
  by_cases hiE : i ∈ edgeComponent ends K zero
  · simp [hiE]
  · have hnot : i ∉ canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y :=
      fun hi => hiE (hcomponent hi)
    by_cases hix : i ∈ canonicalNormalRow ends m k zero x <;>
      by_cases hiy : i ∈ canonicalNormalRow ends m k zero y <;>
      simp [Finset.mem_sdiff, Finset.mem_symmDiff,
        hiE, hix, hiy] at hnot ⊢

theorem not_mem_symmDiff_iff_mem_iff
    (A B : Finset I) (i : I) : i ∉ A ∆ B ↔ (i ∈ A ↔ i ∈ B) := by
  classical
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
    simp [Finset.mem_symmDiff, hiA, hiB]

set_option maxHeartbeats 1000000 in


theorem transfer_pair_parity_of_translatedRow_eq_of_root_incident
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r s x y : leftMaskFiber ends m j k l zero p)
    (hrs : canonicalTranslatedRow ends m k zero r.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero s.1.1 y.1.1)
    {i : I} (him : i ∈ m) (hroot : k ∈ ends i ∨ zero ∈ ends i) :
    (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1) ↔
      i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆
        canonicalTransferUnion ends m k zero y.1.1 := by
  have hnormal := canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r.1.1 s.1.1 x.1.1 y.1.1 hrs
  have hsame :
      (i ∈ canonicalNormalRow ends m k zero x.1.1) ↔
        i ∈ canonicalNormalRow ends m k zero y.1.1 := by
    rcases hroot with hik | hiz
    · exact iff_of_true
        (mem_canonicalNormalRow_of_mem_k hloop hjk hkl x.1.2 him hik)
        (mem_canonicalNormalRow_of_mem_k hloop hjk hkl y.1.2 him hik)
    · exact iff_of_false
        (fun hi => (canonicalNormalRow_no_incident_zero hloop hjk hkl
          x.1.2 i hi) hiz)
        (fun hi => (canonicalNormalRow_no_incident_zero hloop hjk hkl
          y.1.2 i hi) hiz)
  have hnot : i ∉ canonicalNormalRow ends m k zero x.1.1 ∆
      canonicalNormalRow ends m k zero y.1.1 :=
    (not_mem_symmDiff_iff_mem_iff _ _ i).mpr hsame
  rw [hnormal] at hnot
  have hgroup :
      canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1 ∆
          canonicalTransferUnion ends m k zero x.1.1 ∆
          canonicalTransferUnion ends m k zero y.1.1 =
        (canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1) ∆
        (canonicalTransferUnion ends m k zero x.1.1 ∆
          canonicalTransferUnion ends m k zero y.1.1) := by ac_rfl
  rw [hgroup] at hnot
  exact (not_mem_symmDiff_iff_mem_iff _ _ i).mp hnot


theorem transfer_pair_parity_of_not_mem_total
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r s x y : leftMaskFiber ends m j k l zero p)
    {i : I} (him : i ∉ m) :
    (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1) ↔
      i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆
        canonicalTransferUnion ends m k zero y.1.1 := by
  have hr : i ∉ canonicalTransferUnion ends m k zero r.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl r hi)
  have hs : i ∉ canonicalTransferUnion ends m k zero s.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl s hi)
  have hx : i ∉ canonicalTransferUnion ends m k zero x.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl x hi)
  have hy : i ∉ canonicalTransferUnion ends m k zero y.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl y hi)
  simp [Finset.mem_symmDiff, hr, hs, hx, hy]


theorem exists_opposite_badQuadrangle_of_coverage_card_le
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b)
    (hcard : #(canonicalMaskOrbitCoverage ends m j k l zero p a) ≤
      #(canonicalMaskOrbitCoverage ends m j k l zero p b)) :
    ∃ d, d ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p b a := by
  by_contra h
  have hempty : canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p b a = ∅ := by
    exact Finset.eq_empty_iff_forall_notMem.mpr fun d hd => h ⟨d, hd⟩
  have hlt := coverage_card_lt_of_mem_bad_of_opposite_bad_eq_empty
    ends m j k l zero hloop hjk hkl p a b c hab hc hempty
  exact (Nat.not_lt_of_ge hcard) hlt


theorem canonicalCoverageExclusiveBadQuadrangle_typedData
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    CanonicalMaskTransferOrbit ends m j k l zero p a c ∧
      CanonicalMaskTransferOrbit ends m j k l zero p b c ∧
      CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 d ∧
      ((connK ends (rowClass m d 0) k zero ∧
          sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
          sources ends (rowClass m d 0 \
            edgeComponent ends (rowClass m d 0) zero) = ∅ ∧
          Disjoint (canonicalTransferUnion ends m k zero d)
            (rowClass m d 0 \
              edgeComponent ends (rowClass m d 0) zero)) ∨
        (connK ends (rowClass m d 1) k zero ∧
          sources ends (edgeComponent ends (rowClass m d 1) k) = {k, l} ∧
          sources ends (rowClass m d 1 \
            edgeComponent ends (rowClass m d 1) k) = ∅ ∧
          Disjoint (canonicalTransferUnion ends m k zero d)
            (rowClass m d 1 \
              edgeComponent ends (rowClass m d 1) k))) := by
  dsimp only
  have hc' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p a b c).mp hc
  have hac := (mem_canonicalMaskOrbitCoverage_iff
    ends m j k l zero p a c).mp hc'.1
  have hbcOrbit : CanonicalMaskTransferOrbit
      ends m j k l zero p b c :=
    (canonicalMaskTransferOrbit_symm
      ends m j k l zero p hab).trans hac.1
  have hbc : ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 := by
    intro hworks
    exact hc'.2.1 ((mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p b c).mpr ⟨hbcOrbit, hworks⟩)
  refine ⟨hac.1, hbcOrbit, hac.2, hbc,
    canonicalTransferWorks_quadrangleCompletion
      ends m k zero a.1.1 b.1.1 c.1.1 hac.2, ?_⟩
  rcases canonicalQuadrangleCompletion_failedGate_boundaryCertificate
      hloop hjk hkl a b c hc'.2.2 with hzero | hone
  · exact Or.inl ⟨hzero.1, hzero.2.1, hzero.2.2,
      canonicalTransferUnion_disjoint_nonrootRowZero
        ends m k zero _⟩
  · rcases hone with ⟨hconn, hsrc, hcompl⟩
    have heq : edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k =
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) zero :=
      edgeComponent_eq_of_conn ends _ k zero hconn
    exact Or.inr ⟨hconn, (congrArg (sources ends) heq).trans hsrc,
      by rwa [heq],
      canonicalTransferUnion_disjoint_nonrootRowOne
        ends m k zero _⟩


theorem canonicalCoverageExclusiveBadQuadrangle_nonroot_noRootIncidence
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    (∀ i ∈ rowClass m d 0 \
        edgeComponent ends (rowClass m d 0) zero,
        k ∉ ends i ∧ zero ∉ ends i) ∨
      (∀ i ∈ rowClass m d 1 \
        edgeComponent ends (rowClass m d 1) k,
        k ∉ ends i ∧ zero ∉ ends i) := by
  dsimp only
  have hc' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p a b c).mp hc
  rcases canonicalQuadrangleCompletion_failedGate_boundaryCertificate
      hloop hjk hkl a b c hc'.2.2 with hzero | hone
  · left
    intro i hi
    constructor
    · exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ zero k hi
          (connK_symm ends _ hzero.1)
    · exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ zero zero hi Relation.ReflTransGen.refl
  · right
    intro i hi
    have heq : edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k =
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) zero :=
      edgeComponent_eq_of_conn ends _ k zero hone.1
    constructor
    · exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ k k hi Relation.ReflTransGen.refl
    · rw [heq] at hi
      exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ zero zero hi Relation.ReflTransGen.refl


theorem exists_transfer_symmDiff_eq_normalRow_symmDiff_of_adjacent
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (x y : leftMaskFiber ends m j k l zero p)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y) :
    ∃ r s : leftMaskFiber ends m j k l zero p,
      canonicalNormalRow ends m k zero x.1.1 ∆
          canonicalNormalRow ends m k zero y.1.1 =
        canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1 ∆
          canonicalTransferUnion ends m k zero x.1.1 ∆
          canonicalTransferUnion ends m k zero y.1.1 := by
  obtain ⟨r, s, -, -, hrs⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  refine ⟨r, s, ?_⟩
  exact canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r.1.1 s.1.1 x.1.1 y.1.1 hrs


theorem sdiff_eq_sdiff_of_symmDiff_subset
    (A B E : Finset I) (hAB : A ∆ B ⊆ E) : A \ E = B \ E := by
  classical
  ext i
  by_cases hiE : i ∈ E
  · simp [hiE]
  · have hiSame : i ∈ A ↔ i ∈ B := by
      by_contra h
      have hiAB : i ∈ A ∆ B := by
        simp only [Finset.mem_symmDiff]
        tauto
      exact hiE (hAB hiAB)
    simp [hiE, hiSame]


theorem fourfold_symmDiff_subset_of_outside_pair_membership
    (A B C D E : Finset I)
    (hout : ∀ i, i ∉ E -> (i ∈ A ∆ B ↔ i ∈ C ∆ D)) :
    A ∆ B ∆ C ∆ D ⊆ E := by
  classical
  intro i hi
  by_contra hiE
  have hpairs := hout i hiE
  simp only [Finset.mem_symmDiff] at hi hpairs
  tauto


theorem canonicalNormalRow_symmDiff_subset_of_translatedRow_eq
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hrs : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y)
    (hout : ∀ i, i ∉ K ->
      (i ∈ canonicalTransferUnion ends m k zero r ∆
          canonicalTransferUnion ends m k zero s ↔
        i ∈ canonicalTransferUnion ends m k zero x ∆
          canonicalTransferUnion ends m k zero y)) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y ⊆ K := by
  rw [canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r s x y hrs]
  exact fourfold_symmDiff_subset_of_outside_pair_membership
    _ _ _ _ K hout


theorem canonicalNormalRow_symmDiff_subset_canonicalQuadrangleRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) (rho : Fin 2)
    (K : Finset I)
    (hK : K = rowClass m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) rho)
    (r s x y : ↑m -> Fin 4)
    (hrs : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y)
    (href : ∀ i, i ∉ K ->
      (i ∈ canonicalTransferUnion ends m k zero r ∆
          canonicalTransferUnion ends m k zero s ↔
        i ∈ rowClass m c.1.1 rho))
    (hend : ∀ i, i ∉ K ->
      (i ∈ canonicalTransferUnion ends m k zero x ∆
          canonicalTransferUnion ends m k zero y ↔
        i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1)) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y ⊆ K := by
  apply canonicalNormalRow_symmDiff_subset_of_translatedRow_eq
    ends m K k zero r s x y hrs
  intro i hiK
  have hiRow : i ∉ rowClass m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) rho := by
    rw [← hK]
    exact hiK
  calc
    (i ∈ canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s) ↔
        i ∈ rowClass m c.1.1 rho := href i hiK
    _ ↔ i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 :=
      rowClass_pair_parity_of_not_mem_canonicalQuadrangleCompletion
        hloop hjk hkl a b c rho hiRow
    _ ↔ i ∈ canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y := (hend i hiK).symm


theorem canonicalNormalRow_sdiff_eq_of_adjacent_of_outside_transfer_membership
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (E : Finset I)
    (x y : leftMaskFiber ends m j k l zero p)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y)
    (hcancel : ∀ r s : leftMaskFiber ends m j k l zero p,
      canonicalTranslatedRow ends m k zero r.1.1 x.1.1 =
          canonicalTranslatedRow ends m k zero s.1.1 y.1.1 ->
        ∀ i, i ∉ E ->
          (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
              canonicalTransferUnion ends m k zero s.1.1 ↔
            i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆
              canonicalTransferUnion ends m k zero y.1.1)) :
    canonicalNormalRow ends m k zero x.1.1 \ E =
      canonicalNormalRow ends m k zero y.1.1 \ E := by
  obtain ⟨r, s, -, -, hrs⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  have hnormal := canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r.1.1 s.1.1 x.1.1 y.1.1 hrs
  apply sdiff_eq_sdiff_of_symmDiff_subset
  rw [hnormal]
  exact fourfold_symmDiff_subset_of_outside_pair_membership
    _ _ _ _ E (hcancel r s hrs)


theorem canonicalNormalRow_sdiff_eq_of_orbit_of_adjacent
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (E : Finset I)
    (hstep : ∀ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
        canonicalNormalRow ends m k zero x.1.1 \ E =
          canonicalNormalRow ends m k zero y.1.1 \ E)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalNormalRow ends m k zero c.1.1 \ E =
      canonicalNormalRow ends m k zero d.1.1 \ E := by
  induction hcd with
  | refl => rfl
  | @tail x y _ hxy ih => exact ih.trans (hstep x y hxy)


theorem symmDiff_subset_union_symmDiff
    (A B C : Finset I) : A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
  classical
  intro i hi
  simp only [Finset.mem_symmDiff, Finset.mem_union] at hi ⊢
  tauto


theorem canonicalNormalRow_symmDiff_subset_of_orbit_of_adjacent
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (E : Finset I)
    (hstep : ∀ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
        canonicalNormalRow ends m k zero x.1.1 ∆
          canonicalNormalRow ends m k zero y.1.1 ⊆ E)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalNormalRow ends m k zero c.1.1 ∆
      canonicalNormalRow ends m k zero d.1.1 ⊆ E := by
  induction hcd with
  | refl => simp
  | @tail x y hcx hxy ih =>
      exact (symmDiff_subset_union_symmDiff
        (canonicalNormalRow ends m k zero c.1.1)
        (canonicalNormalRow ends m k zero x.1.1)
        (canonicalNormalRow ends m k zero y.1.1)).trans
          (Finset.union_subset ih (hstep x y hxy))

end StatMech.GrahamGHS.FourColor
