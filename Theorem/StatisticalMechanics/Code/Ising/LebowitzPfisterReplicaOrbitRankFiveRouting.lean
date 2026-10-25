/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveRouting


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCurrentFoldedEdge_isDiag_iff_exists_seam
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    (lpReplicaCurrentFoldedEdge G sites e).IsDiag ↔
      ∃ i, e.1 = lpReplicaCurrentSeamEdge sites i := by
  constructor
  · intro hdiag
    induction hval : e.1 using Sym2.inductionOn with
    | _ x y =>
        have hxy : (lpReplicaCurrentGraph G sites).Adj x y := by
          have hmem := e.2
          rw [SimpleGraph.mem_edgeFinset, hval, SimpleGraph.mem_edgeSet] at hmem
          exact hmem
        unfold lpReplicaCurrentFoldedEdge at hdiag
        rw [hval, Sym2.map_mk, Sym2.mk_isDiag_iff] at hdiag
        rcases x with (x | g) <;> rcases y with (y | h)
        · rcases x with x | x <;> rcases y with y | y
          · simp only [lpReplicaCurrentFold] at hdiag
            have hxy' : x = y := Sum.inl.inj hdiag
            subst y
            exact False.elim
              ((lpReplicaCurrentGraph G sites).loopless.irrefl _ hxy)
          · simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hdiag
            rw [lpReplicaCurrentGraph_adj_left_right_iff] at hxy
            obtain ⟨i, hix, hiy⟩ := hxy
            subst x
            subst y
            exact ⟨i, rfl⟩
          · simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hdiag
            rw [(lpReplicaCurrentGraph G sites).adj_comm,
              lpReplicaCurrentGraph_adj_left_right_iff] at hxy
            obtain ⟨i, hiy, hix⟩ := hxy
            subst x
            subst y
            exact ⟨i, by
              unfold lpReplicaCurrentSeamEdge lpReplicaCurrentLeft
                lpReplicaCurrentRight
              rw [Sym2.eq_iff]
              exact Or.inr ⟨rfl, rfl⟩⟩
          · simp only [lpReplicaCurrentFold] at hdiag
            have hxy' : x = y := Sum.inl.inj hdiag
            subst y
            exact False.elim
              ((lpReplicaCurrentGraph G sites).loopless.irrefl _ hxy)
        · rcases x with x | x <;> cases h <;>
            simp only [lpReplicaCurrentFold, Sum.inl_ne_inr] at hdiag
        · cases g <;> rcases y with y | y <;>
            simp only [lpReplicaCurrentFold, Sum.inr_ne_inl] at hdiag
        · cases g <;> cases h <;>
            simp [lpReplicaCurrentGraph, lpReplicaCurrentRel] at hxy
  · rintro ⟨i, hi⟩
    unfold lpReplicaCurrentFoldedEdge
    rw [hi]
    unfold lpReplicaCurrentSeamEdge lpReplicaCurrentLeft
      lpReplicaCurrentRight
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
    rfl


theorem lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k t : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    lpReplicaCurrentLeft sites t ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      t = i ∨ t = j ∨ t = k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff, hsite.eq_iff, hsij, hsij.symm,
    hsik, hsik.symm, hsjk, hsjk.symm]
  constructor
  · rintro (⟨(⟨hti, _⟩ | ⟨htj, _⟩), _⟩ | ⟨htk, _, _⟩)
    · exact Or.inl hti
    · exact Or.inr (Or.inl htj)
    · exact Or.inr (Or.inr htk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hij⟩, hik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hij⟩, hjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hik hki.symm),
        fun hkj => False.elim (hjk hkj.symm)⟩


theorem lpReplicaCurrentRight_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k t : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    lpReplicaCurrentRight sites t ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      t = i ∨ t = j ∨ t = k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff, hsite.eq_iff, hsij, hsij.symm,
    hsik, hsik.symm, hsjk, hsjk.symm]
  constructor
  · rintro (⟨(⟨hti, _⟩ | ⟨htj, _⟩), _⟩ | ⟨htk, _, _⟩)
    · exact Or.inl hti
    · exact Or.inr (Or.inl htj)
    · exact Or.inr (Or.inr htk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hij⟩, hik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hij⟩, hjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hik hki.symm),
        fun hkj => False.elim (hjk hkj.symm)⟩

theorem lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : V) :
    (.inl (.inl x) : LPReplicaCurrentVertex V) ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      x = sites i ∨ x = sites j ∨ x = sites k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]
  constructor
  · rintro (⟨(⟨hxi, _⟩ | ⟨hxj, _⟩), _⟩ | ⟨hxk, _, _⟩)
    · exact Or.inl hxi
    · exact Or.inr (Or.inl hxj)
    · exact Or.inr (Or.inr hxk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hsij⟩, hsik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hsij⟩, hsjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hsik hki.symm),
        fun hkj => False.elim (hsjk hkj.symm)⟩

theorem lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : V) :
    (.inl (.inr x) : LPReplicaCurrentVertex V) ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      x = sites i ∨ x = sites j ∨ x = sites k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]
  constructor
  · rintro (⟨(⟨hxi, _⟩ | ⟨hxj, _⟩), _⟩ | ⟨hxk, _, _⟩)
    · exact Or.inl hxi
    · exact Or.inr (Or.inl hxj)
    · exact Or.inr (Or.inr hxk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hsij⟩, hsik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hsij⟩, hsjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hsik hki.symm),
        fun hkj => False.elim (hsjk hkj.symm)⟩


theorem lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : LPReplicaCurrentVertex V)
    (hx : x ∈ lpReplicaTripleSeamGhostSource sites i j k)
    (hx0 : x ≠ lpReplicaCurrentGhost0)
    (hx1 : x ≠ lpReplicaCurrentGhost1) :
    ∃ u, (u = i ∨ u = j ∨ u = k) ∧
      lpReplicaCurrentFold x = Sum.inl (sites u) := by
  rcases x with (x | b)
  · rcases x with x | x
    · have hx' := (lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk x).mp hx
      rcases hx' with h | h | h
      · exact ⟨i, Or.inl rfl, by simpa [h]⟩
      · exact ⟨j, Or.inr (Or.inl rfl), by simpa [h]⟩
      · exact ⟨k, Or.inr (Or.inr rfl), by simpa [h]⟩
    · have hx' := (lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk x).mp hx
      rcases hx' with h | h | h
      · exact ⟨i, Or.inl rfl, by simpa [h]⟩
      · exact ⟨j, Or.inr (Or.inl rfl), by simpa [h]⟩
      · exact ⟨k, Or.inr (Or.inr rfl), by simpa [h]⟩
  · cases b
    · exact False.elim (hx0 rfl)
    · exact False.elim (hx1 rfl)


theorem lpReplicaCurrentGhost0_mem_tripleSeamGhostSource
    (sites : I -> V) (i j k : I) :
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpReplicaTripleSeamGhostSource sites i j k := by
  simp [lpReplicaTripleSeamGhostSource, lpMatchingSeamSource,
    lpMatchingGhostSource, lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]

theorem lpReplicaCurrentGhost1_mem_tripleSeamGhostSource
    (sites : I -> V) (i j k : I) :
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈
      lpReplicaTripleSeamGhostSource sites i j k := by
  simp [lpReplicaTripleSeamGhostSource, lpMatchingSeamSource,
    lpMatchingGhostSource, lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]


theorem lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 4)
    (hsupport :
      K.biUnion (fun e =>
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m e).toFinset) =
        lpReplicaTripleSeamGhostSource sites i j k)
    (hunique : ∀ x ∈ lpReplicaTripleSeamGhostSource sites i j k,
      ∃! e, e ∈ K ∧ x ∈
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m e).toFinset)
    (hnoI : ∀ e ∈ K, e.1.1 ≠ lpReplicaCurrentSeamEdge sites i)
    (hnoJ : ∀ e ∈ K, e.1.1 ≠ lpReplicaCurrentSeamEdge sites j) :
    ∃ e ∈ K,
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) m e ∧
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) m e ∧
        ¬ (lpReplicaCurrentFoldedEdge G sites e.1).IsDiag := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let A := K.filter fun e =>
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ E e ∨
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ E e
  let D := K.filter fun e =>
    (lpReplicaCurrentFoldedEdge G sites e.1).IsDiag
  obtain ⟨c0, hc0, hc0unique⟩ := hunique lpReplicaCurrentGhost0
    (lpReplicaCurrentGhost0_mem_tripleSeamGhostSource sites i j k)
  obtain ⟨c1, hc1, hc1unique⟩ := hunique lpReplicaCurrentGhost1
    (lpReplicaCurrentGhost1_mem_tripleSeamGhostSource sites i j k)
  have hAsub : A ⊆ {c0, c1} := by
    intro e heA
    obtain ⟨heK, heghost⟩ := Finset.mem_filter.mp heA
    rcases heghost with he0 | he1
    · have heq : e = c0 := hc0unique e
        ⟨heK, Sym2.mem_toFinset.mpr he0⟩
      simp [heq]
    · have heq : e = c1 := hc1unique e
        ⟨heK, Sym2.mem_toFinset.mpr he1⟩
      simp [heq]
  have hAcard : A.card ≤ 2 := by
    exact (Finset.card_le_card hAsub).trans Finset.card_le_two
  have seamK_of_mem_D {e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m} (heD : e ∈ D) :
      e.1.1 = lpReplicaCurrentSeamEdge sites k := by
    obtain ⟨heK, hediag⟩ := Finset.mem_filter.mp heD
    obtain ⟨t, het⟩ :=
      (lpReplicaCurrentFoldedEdge_isDiag_iff_exists_seam
        G sites e.1).mp hediag
    have hleftEnds : lpReplicaCurrentLeft sites t ∈ E e := by
      change lpReplicaCurrentLeft sites t ∈ e.1.1
      rw [het]
      simp [lpReplicaCurrentSeamEdge]
    have hleftBoundary : lpReplicaCurrentLeft sites t ∈
        lpReplicaTripleSeamGhostSource sites i j k := by
      rw [← hsupport]
      apply Finset.mem_biUnion.mpr
      exact ⟨e, heK, Sym2.mem_toFinset.mpr hleftEnds⟩
    have ht := (lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff
      sites hsite hij hik hjk).mp hleftBoundary
    rcases ht with rfl | rfl | rfl
    · exact False.elim (hnoI e heK het)
    · exact False.elim (hnoJ e heK het)
    · exact het
  have hDcard : D.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro e heD f hfD
    have heK := (Finset.mem_filter.mp heD).1
    have hfK := (Finset.mem_filter.mp hfD).1
    have heSeam := seamK_of_mem_D heD
    have hfSeam := seamK_of_mem_D hfD
    have hleftBoundary : lpReplicaCurrentLeft sites k ∈
        lpReplicaTripleSeamGhostSource sites i j k :=
      (lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk).mpr (Or.inr (Or.inr rfl))
    obtain ⟨d, hd, hdunique⟩ := hunique
      (lpReplicaCurrentLeft sites k) hleftBoundary
    have heLeft : lpReplicaCurrentLeft sites k ∈ E e := by
      change lpReplicaCurrentLeft sites k ∈ e.1.1
      rw [heSeam]
      simp [lpReplicaCurrentSeamEdge]
    have hfLeft : lpReplicaCurrentLeft sites k ∈ E f := by
      change lpReplicaCurrentLeft sites k ∈ f.1.1
      rw [hfSeam]
      simp [lpReplicaCurrentSeamEdge]
    exact (hdunique e ⟨heK, Sym2.mem_toFinset.mpr heLeft⟩).trans
      (hdunique f ⟨hfK, Sym2.mem_toFinset.mpr hfLeft⟩).symm
  have hADcard : (A ∪ D).card ≤ 3 :=
    (Finset.card_union_le A D).trans (by omega)
  have hnotSubset : ¬ K ⊆ A ∪ D := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hKcard] at hle
    omega
  have hex : ∃ e, e ∈ K ∧ e ∉ A ∪ D := by
    by_contra h
    apply hnotSubset
    intro e heK
    by_contra heAD
    rw [not_exists] at h
    exact h e ⟨heK, heAD⟩
  obtain ⟨e, heK, heAD⟩ := hex
  have heA : e ∉ A := by
    intro he
    exact heAD (Finset.mem_union_left D he)
  have heD : e ∉ D := by
    intro he
    exact heAD (Finset.mem_union_right A he)
  have heghost : ¬ ((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ E e ∨
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ E e) := by
    intro h
    apply heA
    exact Finset.mem_filter.mpr ⟨heK, h⟩
  refine ⟨e, heK, ?_, ?_, ?_⟩
  · exact fun h => heghost (Or.inl h)
  · exact fun h => heghost (Or.inr h)
  · intro hdiag
    apply heD
    exact Finset.mem_filter.mpr ⟨heK, hdiag⟩


theorem lpReplica_strictPhysicalRoute_folded_labels
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hsupport :
      K.biUnion (fun e =>
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m e).toFinset) =
        lpReplicaTripleSeamGhostSource sites i j k)
    (d : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (hdK : d ∈ K)
    (hd0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
      StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m d)
    (hd1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
      StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m d)
    (hddiag : ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag) :
    ∃ u v,
      (u = i ∨ u = j ∨ u = k) ∧
      (v = i ∨ v = j ∨ v = k) ∧
      u ≠ v ∧
      lpReplicaCurrentFoldedEdge G sites d.1 =
        s(Sum.inl (sites u), Sum.inl (sites v)) := by
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  induction hval : d.1.1 using Sym2.inductionOn with
  | _ x y =>
      have hxEnds : x ∈ E d := by
        change x ∈ d.1.1
        rw [hval]
        simp
      have hyEnds : y ∈ E d := by
        change y ∈ d.1.1
        rw [hval]
        simp
      have hxBoundary : x ∈ lpReplicaTripleSeamGhostSource sites i j k := by
        rw [← hsupport]
        exact Finset.mem_biUnion.mpr
          ⟨d, hdK, Sym2.mem_toFinset.mpr hxEnds⟩
      have hyBoundary : y ∈ lpReplicaTripleSeamGhostSource sites i j k := by
        rw [← hsupport]
        exact Finset.mem_biUnion.mpr
          ⟨d, hdK, Sym2.mem_toFinset.mpr hyEnds⟩
      have hx0 : x ≠ lpReplicaCurrentGhost0 := fun h => hd0 (h ▸ hxEnds)
      have hx1 : x ≠ lpReplicaCurrentGhost1 := fun h => hd1 (h ▸ hxEnds)
      have hy0 : y ≠ lpReplicaCurrentGhost0 := fun h => hd0 (h ▸ hyEnds)
      have hy1 : y ≠ lpReplicaCurrentGhost1 := fun h => hd1 (h ▸ hyEnds)
      obtain ⟨u, hu, hxu⟩ :=
        lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource
          sites hsite hij hik hjk x hxBoundary hx0 hx1
      obtain ⟨v, hv, hyv⟩ :=
        lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource
          sites hsite hij hik hjk y hyBoundary hy0 hy1
      have hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
          s(Sum.inl (sites u), Sum.inl (sites v)) := by
        unfold lpReplicaCurrentFoldedEdge
        rw [hval, Sym2.map_mk, hxu, hyv]
      have huv : u ≠ v := by
        intro huv
        subst v
        apply hddiag
        rw [hfold, Sym2.mk_isDiag_iff]
      exact ⟨u, v, hu, hv, huv, hfold⟩


end
end StatMech.Ising
