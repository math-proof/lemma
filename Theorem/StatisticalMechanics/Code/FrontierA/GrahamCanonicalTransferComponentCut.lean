/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem edgeComponent_eq_grahamSuperpositionBondComponent
    (ends : I -> Sym2 W) (K : Finset I) (u : W) :
    edgeComponent ends K u =
      StatMech.FrontierA.grahamSuperpositionBondComponent ends K u := by
  classical
  ext i
  rw [edgeComponent, Finset.mem_filter,
    StatMech.FrontierA.grahamSuperpositionBondComponent,
    StatMech.Walls.gh4_mem_bondCompOf]
  constructor
  · rintro ⟨hiK, hi⟩
    let x := (ends i).out.1
    exact ⟨hiK, x, Sym2.out_fst_mem (ends i),
      hi x (Sym2.out_fst_mem (ends i))⟩
  · rintro ⟨hiK, x, hx, hux⟩
    refine ⟨hiK, ?_⟩
    intro y hy
    by_cases hxy : x = y
    · simpa [hxy] using hux
    · exact hux.tail ⟨i, hiK, hx, hy, hxy⟩


theorem mem_sdiff_edgeComponent_iff_edgeInside_componentComplement
    (ends : I -> Sym2 W) (K : Finset I) (u : W) {i : I} :
    i ∈ K \ edgeComponent ends K u ↔
      i ∈ K ∧
        edgeInsideK ends
          (StatMech.FrontierA.grahamComponentComplement ends K u) i := by
  rw [edgeComponent_eq_grahamSuperpositionBondComponent]
  exact StatMech.FrontierA.mem_sdiff_component_iff_edgeInsideK_complement
    ends K u


theorem edgeComponentComplement_noCrossing_of_subset
    (ends : I -> Sym2 W) (K L : Finset I) (u : W) (hLK : L ⊆ K) :
    NoCrossingK ends L
      (StatMech.FrontierA.grahamComponentComplement ends K u) :=
  StatMech.FrontierA.grahamComponentComplement_noCrossing_of_subset
    ends K L u hLK


theorem connK_mem_of_noCrossing
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W} {u x : W}
    (hcross : NoCrossingK ends K S) (hu : u ∈ S)
    (hux : connK ends K u x) : x ∈ S := by
  induction hux with
  | refl => exact hu
  | @tail a b _ hstep ih =>
      obtain ⟨i, hiK, ha, hb, -⟩ := hstep
      rcases hcross i hiK with hin | hout
      · exact hin b hb
      · exact False.elim ((Finset.mem_compl.mp (hout a ha)) ih)


theorem connK_not_mem_of_noCrossing
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W} {u x : W}
    (hcross : NoCrossingK ends K S) (hu : u ∉ S)
    (hux : connK ends K u x) : x ∉ S := by
  intro hx
  exact hu (connK_mem_of_noCrossing hcross hx
    (connK_symm ends K hux))


theorem exists_crossing_edge_mem_sdiff_of_connK
    {ends : I -> Sym2 W} {K L : Finset I} {S : Finset W} {u x : W}
    (hcross : NoCrossingK ends K S) (hu : u ∉ S) (hx : x ∈ S)
    (hux : connK ends L u x) :
    ∃ i, i ∈ L \ K ∧
      ∃ a b, a ∈ ends i ∧ b ∈ ends i ∧ a ∉ S ∧ b ∈ S := by
  have crossing : ∀ y, connK ends L u y -> y ∈ S ->
      ∃ i, i ∈ L \ K ∧
        ∃ a b, a ∈ ends i ∧ b ∈ ends i ∧ a ∉ S ∧ b ∈ S := by
    intro y huy hy
    induction huy with
    | refl => exact False.elim (hu hy)
    | @tail a b hab hstep ih =>
        obtain ⟨i, hiL, ha, hb, -⟩ := hstep
        by_cases haS : a ∈ S
        · exact ih haS
        · refine ⟨i, Finset.mem_sdiff.mpr ⟨hiL, ?_⟩,
            a, b, ha, hb, haS, hy⟩
          intro hiK
          rcases hcross i hiK with hin | hout
          · exact haS (hin a ha)
          · exact (Finset.mem_compl.mp (hout b hb)) hy
  exact crossing x hux hx


theorem edgeInside_compl_componentComplement_of_mem_edgeComponent
    (ends : I -> Sym2 W) (K : Finset I) (u : W) {i : I}
    (hi : i ∈ edgeComponent ends K u) :
    edgeInsideK ends
      (StatMech.FrontierA.grahamComponentComplement ends K u)ᶜ i := by
  classical
  intro x hx
  apply Finset.mem_compl.mpr
  apply connK_not_mem_of_noCrossing
    (StatMech.FrontierA.grahamComponentComplement_noCrossing ends K u)
    (StatMech.FrontierA.grahamComponentComplement_not_mem ends K u)
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.2 x hx


theorem mem_edgeComponent_iff_edgeInside_compl_componentComplement
    (ends : I -> Sym2 W) (K : Finset I) (u : W) {i : I} :
    i ∈ edgeComponent ends K u ↔
      i ∈ K ∧ edgeInsideK ends
        (StatMech.FrontierA.grahamComponentComplement ends K u)ᶜ i := by
  classical
  constructor
  · intro hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact ⟨hi.1,
      edgeInside_compl_componentComplement_of_mem_edgeComponent
        ends K u (by
          rw [edgeComponent, Finset.mem_filter]
          exact hi)⟩
  · rintro ⟨hiK, hout⟩
    let x := (ends i).out.1
    have hx : x ∈ ends i := Sym2.out_fst_mem (ends i)
    have hxNot : x ∉
        StatMech.FrontierA.grahamComponentComplement ends K u :=
      Finset.mem_compl.mp (hout x hx)
    have hux : connK ends K u x := by
      rw [StatMech.FrontierA.grahamComponentComplement,
        mem_notConnCompK] at hxNot
      exact Classical.byContradiction (fun h => hxNot h)
    exact mem_edgeComponent_of_reachable_endpoint hux hiK hx


theorem not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
    (ends : I -> Sym2 W) (K : Finset I) (u v : W) {i : I}
    (hi : i ∈ K \ edgeComponent ends K u) (huv : connK ends K u v) :
    v ∉ ends i := by
  intro hvi
  have hins := (mem_sdiff_edgeComponent_iff_edgeInside_componentComplement
    ends K u).mp hi |>.2 v hvi
  rw [StatMech.FrontierA.grahamComponentComplement,
    mem_notConnCompK] at hins
  exact hins huv


theorem sources_inter_edgeComponent_and_sdiff_eq_empty
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K) (hDsrc : sources ends D = ∅) :
    sources ends (D ∩ edgeComponent ends K u) = ∅ ∧
      sources ends (D \ edgeComponent ends K u) = ∅ := by
  have hinter : sources ends (D ∩ edgeComponent ends K u) = ∅ := by
    rw [sources_inter_edgeComponent hDK u, hDsrc]
    simp
  refine ⟨hinter, ?_⟩
  have heq : D \ edgeComponent ends K u =
      D \ (D ∩ edgeComponent ends K u) := by
    ext i
    simp
  rw [heq, sources_sdiff_of_subset Finset.inter_subset_left,
    hDsrc, hinter]
  simp


theorem noCrossing_componentComplement_of_subset
    (ends : I -> Sym2 W) (K D : Finset I) (u : W) (hDK : D ⊆ K) :
    NoCrossingK ends D
      (StatMech.FrontierA.grahamComponentComplement ends K u) :=
  edgeComponentComplement_noCrossing_of_subset ends K D u hDK


theorem sources_canonicalTransferUnion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r : leftMaskFiber ends m j k l zero p) :
    sources ends (canonicalTransferUnion ends m k zero r.1.1) =
      {k, l} := by
  have hv := canonicalTransfers_valid hloop hjk hkl r.1.2
  have hdisj : Disjoint
      (canonicalMiddleTransfer ends m r.1.1 k zero)
      (canonicalOuterTransfer ends m r.1.1 k zero) :=
    (middleMask_disjoint_outerMask m r.1.1).mono
      (by simpa only [middleMask] using hv.1)
      (by simpa only [outerMask] using hv.2.1)
  rw [canonicalTransferUnion, sources_union_of_disjoint hdisj,
    hv.2.2.1, hv.2.2.2]
  simp


theorem sources_canonicalNormalRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p) :
    sources ends (canonicalNormalRow ends m k zero c.1.1) =
      {j, k} ∆ {k, l} := by
  rw [canonicalNormalRow, sources_symmDiff,
    (leftPattern_rowBoundaries c.1.2).1,
    sources_canonicalTransferUnion hloop hjk hkl c]


theorem sources_canonicalNormalRow_symmDiff_eq_empty
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) :
    sources ends
      (canonicalNormalRow ends m k zero c.1.1 ∆
        canonicalNormalRow ends m k zero d.1.1) = ∅ := by
  rw [sources_symmDiff,
    sources_canonicalNormalRow hloop hjk hkl c,
    sources_canonicalNormalRow hloop hjk hkl d]
  exact symmDiff_self _


theorem sources_fourfold_canonicalTransferUnion_symmDiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c d : leftMaskFiber ends m j k l zero p) :
    sources ends
      (canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 ∆
        canonicalTransferUnion ends m k zero d.1.1) = ∅ := by
  rw [sources_symmDiff, sources_symmDiff, sources_symmDiff,
    sources_canonicalTransferUnion hloop hjk hkl a,
    sources_canonicalTransferUnion hloop hjk hkl b,
    sources_canonicalTransferUnion hloop hjk hkl c,
    sources_canonicalTransferUnion hloop hjk hkl d]
  simp


theorem sources_canonicalTransferUnion_symmDiff_eq_empty
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b : leftMaskFiber ends m j k l zero p) :
    sources ends
      (canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1) = ∅ := by
  rw [sources_symmDiff,
    sources_canonicalTransferUnion hloop hjk hkl a,
    sources_canonicalTransferUnion hloop hjk hkl b]
  simp


theorem mem_canonicalTransferUnion_iff_rooted_endpoints
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I) :
    i ∈ canonicalTransferUnion ends m k zero c ↔
      (i ∈ rowClass m c 0 ∧
          ∀ x ∈ ends i, connK ends (rowClass m c 0) zero x) ∨
        (i ∈ rowClass m c 1 ∧
          ∀ x ∈ ends i, connK ends (rowClass m c 1) k x) := by
  classical
  rw [canonicalTransferUnion, canonicalTransfers_union]
  simp only [Finset.mem_union, edgeComponent, Finset.mem_filter]


theorem mem_canonicalTransferUnion_iff_rootComponents
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I) :
    i ∈ canonicalTransferUnion ends m k zero c ↔
      i ∈ edgeComponent ends (rowClass m c 0) zero ∨
        i ∈ edgeComponent ends (rowClass m c 1) k := by
  rw [canonicalTransferUnion, canonicalTransfers_union,
    Finset.mem_union]


theorem mem_zeroRootComponent_iff_mem_rowZero_of_mem_canonicalTransferUnion
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I)
    (hi : i ∈ canonicalTransferUnion ends m k zero c) :
    i ∈ edgeComponent ends (rowClass m c 0) zero ↔
      i ∈ rowClass m c 0 := by
  classical
  constructor
  · intro hiz
    rw [edgeComponent, Finset.mem_filter] at hiz
    exact hiz.1
  · intro hi0
    rcases (mem_canonicalTransferUnion_iff_rootComponents
      ends m k zero c i).mp hi with hiz | hik
    · exact hiz
    · have hi1 := hik
      rw [edgeComponent, Finset.mem_filter] at hi1
      have hi1 := hi1.1
      rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
      exact False.elim (hi1.2 hi0)


theorem mem_kRootComponent_iff_not_mem_rowZero_of_mem_canonicalTransferUnion
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I)
    (hi : i ∈ canonicalTransferUnion ends m k zero c) :
    i ∈ edgeComponent ends (rowClass m c 1) k ↔
      i ∉ rowClass m c 0 := by
  classical
  constructor
  · intro hik hi0
    have hi1 := hik
    rw [edgeComponent, Finset.mem_filter] at hi1
    have hi1 := hi1.1
    rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
    exact hi1.2 hi0
  · intro hi0
    rcases (mem_canonicalTransferUnion_iff_rootComponents
      ends m k zero c i).mp hi with hiz | hik
    · have hiz' := hiz
      rw [edgeComponent, Finset.mem_filter] at hiz'
      exact False.elim (hi0 hiz'.1)
    · exact hik


theorem canonicalTransferUnion_disjoint_nonrootRowZero
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) :
    Disjoint (canonicalTransferUnion ends m k zero c)
      (rowClass m c 0 \
        edgeComponent ends (rowClass m c 0) zero) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiT hiOutside
  have hi0 := (Finset.mem_sdiff.mp hiOutside).1
  exact (Finset.mem_sdiff.mp hiOutside).2
    ((mem_zeroRootComponent_iff_mem_rowZero_of_mem_canonicalTransferUnion
      ends m k zero c i hiT).mpr hi0)


theorem canonicalTransferUnion_disjoint_nonrootRowOne
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) :
    Disjoint (canonicalTransferUnion ends m k zero c)
      (rowClass m c 1 \
        edgeComponent ends (rowClass m c 1) k) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiT hiOutside
  have hi1 := (Finset.mem_sdiff.mp hiOutside).1
  rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
  exact (Finset.mem_sdiff.mp hiOutside).2
    ((mem_kRootComponent_iff_not_mem_rowZero_of_mem_canonicalTransferUnion
      ends m k zero c i hiT).mpr hi1.2)


end StatMech.GrahamGHS.FourColor
