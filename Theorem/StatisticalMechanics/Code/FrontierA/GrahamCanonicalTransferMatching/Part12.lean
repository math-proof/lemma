/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part12
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem even_subset_pair_eq_empty_or_pair
    {A : Finset W} {a b : W} (hab : a ≠ b)
    (hsub : A ⊆ {a, b}) (heven : Even A.card) :
    A = ∅ ∨ A = {a, b} := by
  have hle : A.card ≤ 2 := by
    have := Finset.card_le_card hsub
    simpa [hab] using this
  obtain ⟨n, hn⟩ := heven
  by_cases hzero : A.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  · right
    have hcard : A.card = 2 := by omega
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hab, hcard]


theorem canonicalTranslatedRow_subset_m
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    canonicalTranslatedRow ends m k zero r.1.1 c.1.1 ⊆ m := by
  have hrow0sub : rowClass m c.1.1 0 ⊆ m := by
    intro i hi
    rw [rowClass_zero, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact colorClass_subset m c.1.1 0 hi
    · exact colorClass_subset m c.1.1 1 hi
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with hi | hi
  · exact hrow0sub hi.1
  · exact canonicalTransferUnion_subset_m hloop hjk hkl r hi.1


theorem canonicalTranslatedRow_boundaries
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.sources ends
        (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) =
          {j, k} ∆ {k, l} ∧
      StatMech.Sharpness.RandomCurrent.sources ends
        (m \ canonicalTranslatedRow ends m k zero r.1.1 c.1.1) = ∅ := by
  have hrows := leftPattern_rowBoundaries c.1.2
  have hTsrc : StatMech.Sharpness.RandomCurrent.sources ends
      (canonicalTransferUnion ends m k zero r.1.1) = {k, l} := by
    have hv := canonicalTransfers_valid hloop hjk hkl r.1.2
    have hdisj : Disjoint
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) :=
      (middleMask_disjoint_outerMask m r.1.1).mono
        (by simpa only [middleMask] using hv.1)
        (by simpa only [outerMask] using hv.2.1)
    rw [canonicalTransferUnion,
      sources_union_of_disjoint hdisj,
      hv.2.2.1, hv.2.2.2]
    simp
  have hKsrc : StatMech.Sharpness.RandomCurrent.sources ends
      (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) =
        {j, k} ∆ {k, l} := by
    rw [canonicalTranslatedRow,
      StatMech.Sharpness.RandomCurrent.sources_symmDiff,
      hrows.1, hTsrc]
  have hrow0sub : rowClass m c.1.1 0 ⊆ m := by
    intro i hi
    rw [rowClass_zero, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact colorClass_subset m c.1.1 0 hi
    · exact colorClass_subset m c.1.1 1 hi
  have htotal : StatMech.Sharpness.RandomCurrent.sources ends m =
      {j, k} ∆ {k, l} := by
    have hb : {k, l} =
        StatMech.Sharpness.RandomCurrent.sources ends m ∆ {j, k} := by
      rw [← hrows.2, rowClass_one_eq_sdiff,
        sources_sdiff_of_subset hrow0sub, hrows.1]
    calc
      StatMech.Sharpness.RandomCurrent.sources ends m =
          (StatMech.Sharpness.RandomCurrent.sources ends m ∆ {j, k}) ∆
            {j, k} := by simp
      _ = {k, l} ∆ {j, k} := by rw [← hb]
      _ = {j, k} ∆ {k, l} := symmDiff_comm _ _
  have hKsub : canonicalTranslatedRow ends m k zero r.1.1 c.1.1 ⊆ m := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with hi | hi
    · exact hrow0sub hi.1
    · exact canonicalTransferUnion_subset_m hloop hjk hkl r hi.1
  refine ⟨hKsrc, ?_⟩
  rw [sources_sdiff_of_subset hKsub, htotal, hKsrc, symmDiff_self]
  rfl


theorem canonicalTranslatedRow_sourcePair_connected
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.connK ends
      (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) j l := by
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  have hKsub : K ⊆ m := canonicalTranslatedRow_subset_m
    hloop hjk hkl r c
  have hsrc0 := (canonicalTranslatedRow_boundaries
    hloop hjk hkl r c).1
  have hpair : ({j, k} : Finset W) ∆ {k, l} = {j, l} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert,
      Finset.mem_singleton]
    aesop
  have hsrc : StatMech.Sharpness.RandomCurrent.sources ends K =
      {j, l} := by
    rw [hsrc0, hpair]
  exact StatMech.Walls.gc6_pairingPath_abstract ends K K
    (fun i hi => hloop i (hKsub hi)) Finset.Subset.rfl hsrc hjl


theorem canonicalTranslatedRow_conn_source_iff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero u : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.connK ends
        (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) u j ↔
      StatMech.Sharpness.RandomCurrent.connK ends
        (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) u l := by
  have hjlConn := canonicalTranslatedRow_sourcePair_connected
    hloop hjk hkl hjl r c
  constructor
  · exact fun huj => huj.trans hjlConn
  · exact fun hul => hul.trans
      (StatMech.Sharpness.RandomCurrent.connK_symm ends _ hjlConn)


theorem canonicalTranslatedRow_component_sources_empty_or_full
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero u : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
    let A := {j, k} ∆ {k, l}
    StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K u) = ∅ ∨
      StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K u) = A := by
  classical
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  let A : Finset W := {j, k} ∆ {k, l}
  change StatMech.Sharpness.RandomCurrent.sources ends
        (edgeComponent ends K u) = ∅ ∨
    StatMech.Sharpness.RandomCurrent.sources ends
        (edgeComponent ends K u) = A
  have hKsrc : StatMech.Sharpness.RandomCurrent.sources ends K = A :=
    (canonicalTranslatedRow_boundaries hloop hjk hkl r c).1
  have hKsub : K ⊆ m := canonicalTranslatedRow_subset_m
    hloop hjk hkl r c
  have hloopK : ∀ i ∈ K, ¬ (ends i).IsDiag :=
    fun i hi => hloop i (hKsub hi)
  have hEsrc : StatMech.Sharpness.RandomCurrent.sources ends
      (edgeComponent ends K u) =
      A ∩ StatMech.Sharpness.RandomCurrent.compOf ends K u := by
    rw [sources_edgeComponent, hKsrc]
  have hEsubA : StatMech.Sharpness.RandomCurrent.sources ends
      (edgeComponent ends K u) ⊆ A := by
    rw [hEsrc]
    exact Finset.inter_subset_left
  have hEeven : Even (StatMech.Sharpness.RandomCurrent.sources ends
      (edgeComponent ends K u)).card := by
    rw [hEsrc, ← hKsrc]
    exact StatMech.Walls.gc7_componentEven_sources ends K hloopK u
  by_cases hjl : j = l
  · left
    have hpairs : ({j, k} : Finset W) = {k, l} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    have hA : A = ∅ := by
      change {j, k} ∆ {k, l} = ∅
      rw [hpairs]
      exact symmDiff_self _
    exact Finset.eq_empty_iff_forall_notMem.mpr fun x hx =>
      (by simpa [hA] using hEsubA hx)
  · have hA : A = {j, l} := by
      change {j, k} ∆ {k, l} = {j, l}
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_insert,
        Finset.mem_singleton]
      aesop
    have hpair := even_subset_pair_eq_empty_or_pair hjl
      (by simpa [hA] using hEsubA) hEeven
    simpa [hA] using hpair


theorem canonicalTranslatedRow_rootComponent_boundaryCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hcut : CanonicalTranslatedRowRootComponentCut
      ends m k zero r.1.1 c.1.1) :
    let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
    let A := {j, k} ∆ {k, l}
    StatMech.Sharpness.RandomCurrent.sources ends K = A ∧
      StatMech.Sharpness.RandomCurrent.sources ends (m \ K) = ∅ ∧
      ((StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
          edgeComponent ends K zero = edgeComponent ends K k ∧
          ((StatMech.Sharpness.RandomCurrent.sources ends
                (edgeComponent ends K zero) = ∅ ∧
              StatMech.Sharpness.RandomCurrent.sources ends
                (K \ edgeComponent ends K zero) = A) ∨
            (StatMech.Sharpness.RandomCurrent.sources ends
                (edgeComponent ends K zero) = A ∧
              StatMech.Sharpness.RandomCurrent.sources ends
                (K \ edgeComponent ends K zero) = ∅))) ∨
        (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
          edgeComponent ends (m \ K) zero =
            edgeComponent ends (m \ K) k ∧
          StatMech.Sharpness.RandomCurrent.sources ends
            (edgeComponent ends (m \ K) zero) = ∅ ∧
          StatMech.Sharpness.RandomCurrent.sources ends
            ((m \ K) \ edgeComponent ends (m \ K) zero) = ∅)) := by
  classical
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  let A : Finset W := {j, k} ∆ {k, l}
  have hbounds := canonicalTranslatedRow_boundaries hloop hjk hkl r c
  have hKsrc : StatMech.Sharpness.RandomCurrent.sources ends K = A :=
    hbounds.1
  have hLsrc : StatMech.Sharpness.RandomCurrent.sources ends (m \ K) = ∅ :=
    hbounds.2
  have hEsub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hLEsub : edgeComponent ends (m \ K) zero ⊆ m \ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  refine ⟨hKsrc, hLsrc, ?_⟩
  rcases hcut with hcut | hcut
  · left
    refine ⟨hcut.1, hcut.2, ?_⟩
    have hclass : StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K zero) = ∅ ∨
        StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K zero) = A := by
      simpa only [K, A] using
        (canonicalTranslatedRow_component_sources_empty_or_full
          (u := zero) hloop hjk hkl r c)
    rcases hclass with hEempty | hEfull
    · left
      refine ⟨hEempty, ?_⟩
      rw [sources_sdiff_of_subset hEsub, hKsrc, hEempty]
      simp [A]
    · right
      refine ⟨hEfull, ?_⟩
      rw [sources_sdiff_of_subset hEsub, hKsrc, hEfull]
      exact symmDiff_self A
  · right
    refine ⟨hcut.1, hcut.2, ?_, ?_⟩
    · rw [sources_edgeComponent, hLsrc]
      simp
    · rw [sources_sdiff_of_subset hLEsub, hLsrc,
        sources_edgeComponent, hLsrc]
      simp


theorem canonicalTransferWorks_failed_translatedRow_component
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
    (StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
        edgeComponent ends K zero = edgeComponent ends K k) ∨
      (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
        edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k) := by
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  have hdisc : ¬ RowSupportDisconnects ends m K k zero := by
    intro h
    exact hbad ((canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r c).mpr h)
  by_cases hK : StatMech.Sharpness.RandomCurrent.connK ends K k zero
  · exact Or.inl ⟨hK, (edgeComponent_eq_of_conn ends K k zero hK).symm⟩
  · have hcomp : StatMech.Sharpness.RandomCurrent.connK
        ends (m \ K) k zero := by
      by_contra hcomp
      exact hdisc ⟨hK, hcomp⟩
    exact Or.inr ⟨hcomp,
      (edgeComponent_eq_of_conn ends (m \ K) k zero hcomp).symm⟩

theorem canonicalTransferWorks_failed_rootComponentCut
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    CanonicalTranslatedRowRootComponentCut
      ends m k zero r.1.1 c.1.1 :=
  canonicalTransferWorks_failed_translatedRow_component
    hloop hjk hkl r c hbad


theorem canonicalMaskRightAugmentedExposure_failedOpposite_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x u : ↑S) (huc : u ≠ c) (hxu : x ≠ u)
    (hshare : (canonicalMaskRightAugmentedAssignedImage
        ends m j k l zero p S c f hf u huc).1 ∈
      canonicalMaskRightImages ends m j k l zero p x.1) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 u.1.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 u.1.1.1 ∧
      (¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1 ∨
        ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
          q₁ ≠ q₂ ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p u.1) := by
  classical
  let qS := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u huc
  have hqu := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf u huc
  obtain ⟨a, hax, hqa⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p x.1 qS.1).mp hshare
  obtain ⟨b, hbu, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p u.1 qS.1).mp hqu
  have hraw : balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) x.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) u.1.1.1 :=
    hqa.symm.trans hqb
  have htrans := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl a b x.1 u.1).mp hraw
  refine ⟨a, b, hax, hbu, htrans, ?_⟩
  by_cases hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1
  · right
    exact exists_two_common_canonicalMaskRightImages_of_collisionSquare
      hloop hjk hkl a b x.1 u.1 (fun h => hxu (Subtype.ext h))
        hax htrans hbx
  · exact Or.inl hbx


theorem canonicalMaskRightAugmentedExposure_componentCut_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x u : ↑S) (huc : u ≠ c) (hxu : x ≠ u)
    (hshare : (canonicalMaskRightAugmentedAssignedImage
        ends m j k l zero p S c f hf u huc).1 ∈
      canonicalMaskRightImages ends m j k l zero p x.1) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 u.1.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 u.1.1.1 ∧
      (((StatMech.Sharpness.RandomCurrent.connK ends
              (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k zero ∧
            edgeComponent ends
                (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) zero =
              edgeComponent ends
                (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k) ∨
          (StatMech.Sharpness.RandomCurrent.connK ends
              (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1)
                k zero ∧
            edgeComponent ends
                (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) zero =
              edgeComponent ends
                (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k)) ∨
        ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
          q₁ ≠ q₂ ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p u.1) := by
  obtain ⟨a, b, hax, hbu, htrans, hcase⟩ :=
    canonicalMaskRightAugmentedExposure_failedOpposite_or_square
      hloop hjk hkl S c f hf x u huc hxu hshare
  refine ⟨a, b, hax, hbu, htrans, ?_⟩
  rcases hcase with hbad | hsquare
  · exact Or.inl (canonicalTransferWorks_failed_translatedRow_component
      hloop hjk hkl b x.1 hbad)
  · exact Or.inr hsquare


theorem canonicalMaskRightFullExposure_cut_or_secondRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (herase : ∀ x ∈ S,
      canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) =
        canonicalMaskRightNeighborhood ends m j k l zero p S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (u : {u : ↑S // u ≠ c}) :
    (∃ r x : leftMaskFiber ends m j k l zero p,
        x ∈ S ∧ CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 x.1.1) ∨
      ∃ s : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        s ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        s.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 := by
  classical
  let qS := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u.1 u.2
  have hqu := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf u.1 u.2
  obtain ⟨x, hxS, hxu, hqx⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S u.1.1 u.1.2 (herase u.1.1 u.1.2) qS.1 hqu
  let xS : ↑S := ⟨x, hxS⟩
  have hxune : xS ≠ u.1 := by
    intro h
    exact hxu (congrArg Subtype.val h)
  obtain ⟨a, b, hax, hbu, htrans, hcase⟩ :=
    canonicalMaskRightAugmentedExposure_failedOpposite_or_square
      hloop hjk hkl S c f hf xS u.1 u.2 hxune hqx
  rcases hcase with hbad | hsquare
  · left
    exact ⟨b, x, hxS, canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl b x hbad⟩
  · right
    obtain ⟨q₁, q₂, hqne, hq₁x, hq₁u, hq₂x, hq₂u⟩ := hsquare
    by_cases hq₁ : q₁ = qS.1
    · have hq₂S : q₂ ∈ canonicalMaskRightNeighborhood
          ends m j k l zero p S :=
        (mem_canonicalMaskRightNeighborhood_iff
          ends m j k l zero p S q₂).mpr ⟨u.1.1, u.1.2, hq₂u⟩
      let s : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S) := ⟨q₂, hq₂S⟩
      refine ⟨s, ?_, hq₂u⟩
      intro h
      apply hqne
      exact hq₁.trans (congrArg Subtype.val h).symm
    · have hq₁S : q₁ ∈ canonicalMaskRightNeighborhood
          ends m j k l zero p S :=
        (mem_canonicalMaskRightNeighborhood_iff
          ends m j k l zero p S q₁).mpr ⟨u.1.1, u.1.2, hq₁u⟩
      exact ⟨⟨q₁, hq₁S⟩, fun h => hq₁ (congrArg Subtype.val h), hq₁u⟩


theorem canonicalMaskRightFullExposure_secondRows_of_noCut
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (herase : ∀ x ∈ S,
      canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) =
        canonicalMaskRightNeighborhood ends m j k l zero p S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (hnoCut : ∀ r x : leftMaskFiber ends m j k l zero p, x ∈ S ->
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 x.1.1) :
    ∀ u : {u : ↑S // u ≠ c},
      ∃ s : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        s ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        s.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 := by
  intro u
  rcases canonicalMaskRightFullExposure_cut_or_secondRow
      hloop hjk hkl S herase c f hf u with hcut | hsecond
  · obtain ⟨r, x, hxS, hcut⟩ := hcut
    exact (hnoCut r x hxS hcut).elim
  · exact hsecond

set_option maxHeartbeats 1000000 in


theorem canonicalMaskRightMatchingPair_failedOpposite_or_expands
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs
      ends m j k l zero p S c d)
    (x : ↑S) (hxc : x ≠ c)
    (hmove : x ≠ (ef.1.trans ef.2.symm : Equiv.Perm ↑S) x) :
    ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p
        ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1 ∧
      ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧
      CanonicalTransferWorks ends m k zero
        b.1.1 ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero
          b.1.1 ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1.1.1 ∧
      (¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1 ∨
        ∃ r : rightMaskFiber ends m j k l zero p,
          r ≠ q ∧
          r ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          r ∈ canonicalMaskRightImages ends m j k l zero p
            ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1 ∧
          ∃ u v : ↑S,
            u ≠ c ∧ v ≠ d ∧ u ≠ x ∧
            v ≠ (ef.1.trans ef.2.symm : Equiv.Perm ↑S) x ∧
            (ef.1.trans ef.2.symm : Equiv.Perm ↑S) u = v ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p v.1) := by
  classical
  let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
  obtain ⟨q, hqx, hqσ, hdisp⟩ :=
    canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement
      ends m j k l zero p S c d ef hef x hxc
  obtain ⟨a, hax, hqa⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p x.1 q).mp hqx
  obtain ⟨b, hbσ, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p (σ x).1 q).mp hqσ
  have hraw : balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) x.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) (σ x).1.1.1 :=
    hqa.symm.trans hqb
  have htrans := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl a b x.1 (σ x).1).mp hraw
  refine ⟨q, hqx, hqσ, a, b, hax, hbσ, htrans, ?_⟩
  by_cases hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1
  · right
    obtain ⟨q₁, q₂, hqne, hq₁x, hq₁σ, hq₂x, hq₂σ⟩ :=
      exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl a b x.1 (σ x).1
          (fun h => hmove (Subtype.ext h)) hax htrans hbx
    by_cases hq₁q : q₁ = q
    · obtain ⟨u, v, huc, hvd, hux, hvσ, hσuv, hq₂u, hq₂v⟩ :=
        hdisp q₂ (fun h => hqne (hq₁q.trans h.symm)) hq₂x hq₂σ
      exact ⟨q₂, (fun h => hqne (hq₁q.trans h.symm)), hq₂x, hq₂σ, u, v,
        huc, hvd, hux, hvσ, hσuv, hq₂u, hq₂v⟩
    · obtain ⟨u, v, huc, hvd, hux, hvσ, hσuv, hq₁u, hq₁v⟩ :=
        hdisp q₁ hq₁q hq₁x hq₁σ
      exact ⟨q₁, hq₁q, hq₁x, hq₁σ, u, v,
        huc, hvd, hux, hvσ, hσuv, hq₁u, hq₁v⟩
  · exact Or.inl hbx


theorem exists_tight_canonicalMaskRightHall_obstruction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
        (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 =
          S.card ∧
        (∀ c ∈ S,
          canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) =
            canonicalMaskRightNeighborhood ends m j k l zero p S) ∧
        (∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S ->
          T.card ≤ (canonicalMaskRightNeighborhood
            ends m j k l zero p T).card) ∧
        (∀ c ∈ S, ∀ d ∈ S,
          CanonicalMaskTransferOrbit ends m j k l zero p c d) ∧
        (∀ c ∈ S, ∃ d ∈ S, d ≠ c ∧
          CanonicalMaskTransferAdjacent ends m j k l zero p c d) := by
  classical
  rw [CanonicalMaskRightHall] at hfail
  push Not at hfail
  obtain ⟨S₀, hS₀⟩ := hfail
  let bad : Finset (Finset (leftMaskFiber ends m j k l zero p)) :=
    Finset.univ.filter fun S =>
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card < S.card
  have hbad : bad.Nonempty := by
    refine ⟨S₀, ?_⟩
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS₀
  obtain ⟨S, hSbad, hSmin⟩ := bad.exists_min_image Finset.card hbad
  have hlt : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card < S.card := by
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hSbad
  have hSne : S.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hlt)
  have hProperHall : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card := by
    intro T hTS
    by_contra h
    have hTbad : T ∈ bad := by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hmin := hSmin T hTbad
    have hcard := Finset.card_lt_card hTS
    omega
  have hHallEraseAll : ∀ c ∈ S, (S.erase c).card ≤
      (canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c)).card := by
    intro c hc
    have hnotBad : S.erase c ∉ bad := by
      intro hmem
      have hle := hSmin (S.erase c) hmem
      rw [Finset.card_erase_of_mem hc] at hle
      omega
    by_contra h
    apply hnotBad
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have herase : ∀ c ∈ S,
      canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) =
        canonicalMaskRightNeighborhood ends m j k l zero p S := by
    intro c hc
    have hsubset := canonicalMaskRightNeighborhood_mono
      ends m j k l zero p (Finset.erase_subset c S)
    apply Finset.eq_of_subset_of_card_le hsubset
    have hHallErase := hHallEraseAll c hc
    rw [Finset.card_erase_of_mem hc] at hHallErase
    omega
  have htight : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card := by
    obtain ⟨c, hc⟩ := hSne
    have hHallErase := hHallEraseAll c hc
    rw [herase c hc] at hHallErase
    rw [Finset.card_erase_of_mem hc] at hHallErase
    omega
  have horbit : ∀ c ∈ S, ∀ d ∈ S,
      CanonicalMaskTransferOrbit ends m j k l zero p c d := by
    intro c hc d hd
    by_contra hcd
    let A := S.filter fun x =>
      CanonicalMaskTransferOrbit ends m j k l zero p c x
    let B := S \ A
    have hAS : A ⊆ S := Finset.filter_subset _ _
    have hcA : c ∈ A := by
      simp only [A, Finset.mem_filter, hc, true_and]
      exact canonicalMaskTransferOrbit_refl ends m j k l zero p c
    have hdNotA : d ∉ A := by
      simp only [A, Finset.mem_filter, hd, true_and]
      exact hcd
    have hdB : d ∈ B := Finset.mem_sdiff.mpr ⟨hd, hdNotA⟩
    have hcNotB : c ∉ B := fun hcB => (Finset.mem_sdiff.mp hcB).2 hcA
    have hAproper : A ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨hAS, fun hAS' => hdNotA (hAS' ▸ hd)⟩
    have hBproper : B ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.sdiff_subset, fun hBS => hcNotB (hBS ▸ hc)⟩
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp hxB).2 hxA
    have hsep : ∀ a ∈ A, ∀ b ∈ B,
        ¬ CanonicalMaskTransferOrbit ends m j k l zero p a b := by
      intro a haA b hbB hab
      have hca := (Finset.mem_filter.mp haA).2
      have hcb := hca.trans hab
      exact (Finset.mem_sdiff.mp hbB).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hbB).1, hcb⟩)
    have hUnion :=
      card_le_canonicalMaskRightNeighborhood_union_of_orbitSeparated
        ends m j k l zero p A B hAB hsep
          (hProperHall A hAproper) (hProperHall B hBproper)
    rw [Finset.union_sdiff_of_subset hAS] at hUnion
    exact (Nat.not_lt_of_ge hUnion) hlt
  refine ⟨S, hSne, htight, herase, hProperHall, horbit, ?_⟩
  intro c hc
  obtain ⟨q, hqc⟩ := canonicalMaskRightImages_nonempty
    ends m j k l zero hloop hjk hkl hk0 p c
  have hqS : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨c, hc, hqc⟩
  have hqErase : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p (S.erase c) := by
    rw [herase c hc]
    exact hqS
  obtain ⟨d, hdErase, hqd⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p (S.erase c) q).mp hqErase
  have hd := Finset.mem_erase.mp hdErase
  refine ⟨d, hd.2, ?_, ?_⟩
  · exact hd.1
  · exact (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c d).mp ⟨q, hqc, hqd⟩


theorem exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ (S : Finset (leftMaskFiber ends m j k l zero p))
        (a r c : leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧ a ∈ S ∧
      (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card ∧
      (∀ x ∈ S,
        canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) =
          canonicalMaskRightNeighborhood ends m j k l zero p S) ∧
      (∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S ->
        T.card ≤ (canonicalMaskRightNeighborhood
          ends m j k l zero p T).card) ∧
      (∀ d ∈ S,
        CanonicalMaskTransferOrbit ends m j k l zero p a d) ∧
      CanonicalMaskTransferOrbit ends m j k l zero p a r ∧
      (∀ t : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p a t ->
        (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
          (canonicalMaskOrbitCoverage ends m j k l zero p r).card) ∧
      c ∈ S ∧
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p c ∧
      c ∉ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 := by
  classical
  obtain ⟨S, hSne, htight, herase, hproper, horbit, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨a, haS⟩ := hSne
  let O := canonicalMaskTransferOrbitFinset ends m j k l zero p a
  obtain ⟨r, hrO, hrMax⟩ := O.exists_max_image
    (fun x => (canonicalMaskOrbitCoverage ends m j k l zero p x).card)
    (canonicalMaskTransferOrbitFinset_nonempty
      ends m j k l zero p a)
  have har : CanonicalMaskTransferOrbit ends m j k l zero p a r := by
    rwa [mem_canonicalMaskTransferOrbitFinset_iff] at hrO
  have haSorbit : ∀ d ∈ S,
      CanonicalMaskTransferOrbit ends m j k l zero p a d := by
    intro d hdS
    exact horbit a haS d hdS
  have hrMax' : ∀ t : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p a t ->
      (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
        (canonicalMaskOrbitCoverage ends m j k l zero p r).card := by
    intro t hat
    apply hrMax t
    rwa [mem_canonicalMaskTransferOrbitFinset_iff]
  by_cases hworks : ∀ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hbad⟩ := hworks
    have hcCoverage : c ∈ canonicalMaskOrbitCoverage
        ends m j k l zero p c := by
      rw [mem_canonicalMaskOrbitCoverage_iff]
      exact ⟨canonicalMaskTransferOrbit_refl ends m j k l zero p c,
        canonicalTransferWorks_self hloop hjk hkl hk0 c⟩
    have hcNotCoverage : c ∉ canonicalMaskOrbitCoverage
        ends m j k l zero p r := by
      intro hc
      exact hbad ((mem_canonicalMaskOrbitCoverage_iff
        ends m j k l zero p r c).mp hc).2
    exact ⟨S, a, r, c, ⟨a, haS⟩, haS, htight, herase, hproper,
      haSorbit, har, hrMax', hcS, hcCoverage, hcNotCoverage,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl r c hbad⟩


theorem exists_maximalOrbitCoverage_quadrangleDichotomy_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ (S : Finset (leftMaskFiber ends m j k l zero p))
        (a r c : leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧ a ∈ S ∧
      (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card ∧
      (∀ d ∈ S,
        CanonicalMaskTransferOrbit ends m j k l zero p a d) ∧
      CanonicalMaskTransferOrbit ends m j k l zero p a r ∧
      (∀ t : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p a t ->
        (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
          (canonicalMaskOrbitCoverage ends m j k l zero p r).card) ∧
      c ∈ S ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 ∧
      ((∃ d : leftMaskFiber ends m j k l zero p,
          d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
          d ∉ canonicalMaskOrbitCoverage ends m j k l zero p c) ∨
        (c ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p c r ∧
          ∃ d : leftMaskFiber ends m j k l zero p,
            d ∈ canonicalCoverageExclusiveBadQuadrangles
              ends m j k l zero p r c)) := by
  classical
  obtain ⟨S, a, r, c, hSne, haS, htight, -, -, haSorbit,
      har, hrMax, hcS, hcCoverage, hcNotCoverage, hcut⟩ :=
    exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hcr : CanonicalMaskTransferOrbit ends m j k l zero p c r :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p
      (haSorbit c hcS)).trans har
  by_cases hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        c.1.1 r.1.1 c.1.1) k zero
  · let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p c r c hdisc
    have hd := quadrangleCompletion_mem_coverage_sdiff
      hloop hjk hkl c r c hcr hcCoverage hcNotCoverage hdisc
    exact ⟨S, a, r, c, hSne, haS, htight, haSorbit, har, hrMax,
      hcS, hcut, Or.inl ⟨d, hd.1, hd.2⟩⟩
  · have hcBad : c ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p c r := by
      rw [mem_canonicalCoverageExclusiveBadQuadrangles_iff]
      exact ⟨hcCoverage, hcNotCoverage, hdisc⟩
    have hcard := hrMax c (haSorbit c hcS)
    obtain ⟨d, hdBad⟩ :=
      exists_opposite_badQuadrangle_of_coverage_card_le
        hloop hjk hkl c r c hcr hcBad hcard
    exact ⟨S, a, r, c, hSne, haS, htight, haSorbit, har, hrMax,
      hcS, hcut, Or.inr ⟨hcBad, d, hdBad⟩⟩


end StatMech.GrahamGHS.FourColor
