/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFour
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag
    {W ι : Type*} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι]
    (ends : ι -> Sym2 W) (c : ι) (hdiag : ¬ (ends c).IsDiag) :
    StatMech.Sharpness.RandomCurrent.sources ends {c} =
      (ends c).toFinset := by
  induction hends : ends c using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by
        intro h
        subst y
        apply hdiag
        rw [hends]
        exact Sym2.mk_isDiag_iff.mpr rfl
      rw [randomCurrent_sources_singleton_of_ends_eq ends c hxy hends]
      simpa only [hends, Sym2.toFinset_mk_eq]


theorem exists_mem_ends_of_connK_of_ne
    {W ι : Type*} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι]
    (ends : ι -> Sym2 W) (S : Finset ι) {a b : W}
    (hab : a ≠ b)
    (hconn : StatMech.Sharpness.RandomCurrent.connK ends S a b) :
    ∃ e ∈ S, a ∈ ends e := by
  have htrans : Relation.TransGen
      (StatMech.Sharpness.RandomCurrent.adjStep ends S) a b :=
    (Relation.reflTransGen_iff_eq_or_transGen.mp hconn).resolve_left hab.symm
  obtain ⟨x, hstep, _⟩ := Relation.TransGen.head'_iff.mp htrans
  exact ⟨hstep.choose, hstep.choose_spec.1,
    hstep.choose_spec.2.1⟩


theorem randomCurrent_connK_insert_parallel_iff
    {W ι : Type*} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι]
    (ends : ι -> Sym2 W) (K : Finset ι) (c e : ι)
    (he : e ∈ K) (hparallel : ends c = ends e) (a b : W) :
    StatMech.Sharpness.RandomCurrent.connK ends (insert c K) a b ↔
      StatMech.Sharpness.RandomCurrent.connK ends K a b := by
  constructor
  · apply Relation.ReflTransGen.mono
    rintro x y ⟨f, hf, hx, hy, hxy⟩
    by_cases hfc : f = c
    · subst f
      exact ⟨e, he, by simpa only [hparallel] using hx,
        by simpa only [hparallel] using hy, hxy⟩
    · exact ⟨f, (Finset.mem_insert.mp hf).resolve_left hfc,
        hx, hy, hxy⟩
  · exact StatMech.GrahamGHS.FourColor.connK_mono
      (Finset.subset_insert c K)


theorem lpReplica_seam_union_parallelCopies_ghost_disconnected
    (G : SimpleGraph V) (sites : I -> V) (i : I)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c e0 : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (C : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i)
    (hsame : ∀ e ∈ C, e.1.1 = e0.1.1) :
    ¬ StatMech.Sharpness.RandomCurrent.connK
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m)
      ({c} ∪ C) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  intro hconn
  have hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
      lpReplicaCurrentGhost1 := by
    simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  obtain ⟨a, haS, hg0a⟩ := exists_mem_ends_of_connK_of_ne E
    ({c} ∪ C) hghost hconn
  obtain ⟨b, hbS, hg1b⟩ := exists_mem_ends_of_connK_of_ne E
    ({c} ∪ C) hghost.symm
      (StatMech.Sharpness.RandomCurrent.connK_symm E _ hconn)
  have haC : a ∈ C := by
    simp only [Finset.mem_union, Finset.mem_singleton] at haS
    rcases haS with rfl | haC
    · change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ a.1.1 at hg0a
      rw [hc] at hg0a
      simp [lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0] at hg0a
    · exact haC
  have hbC : b ∈ C := by
    simp only [Finset.mem_union, Finset.mem_singleton] at hbS
    rcases hbS with rfl | hbC
    · change (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ b.1.1 at hg1b
      rw [hc] at hg1b
      simp [lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost1] at hg1b
    · exact hbC
  have hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ e0.1.1 := by
    change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ a.1.1 at hg0a
    rw [hsame a haC] at hg0a
    exact hg0a
  have hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ e0.1.1 := by
    change (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ b.1.1 at hg1b
    rw [hsame b hbC] at hg1b
    exact hg1b
  have hedge : e0.1.1 = s((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
      lpReplicaCurrentGhost1) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hg0 hg1 hghost
  have hm := SimpleGraph.mem_edgeFinset.mp e0.1.2
  rw [hedge] at hm
  simpa [lpReplicaCurrentGraph, lpReplicaCurrentRel, lpReplicaCurrentGhost0,
    lpReplicaCurrentGhost1] using hm


theorem lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    lpReplicaToggleRows G sites m (Finset.univ \ {c})
        (lpReplicaSwapRowsTag tag) =
      lpReplicaToggleRows G sites m {c} tag := by
  funext a
  by_cases hac : a = c
  · subst a
    rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, htag]
  · rcases htag : tag a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, htag, hac]

set_option maxHeartbeats 800000 in


theorem lpReplicaRowGate_compl_singleton_currentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (hcurrent : (tag c).2 = false) :
    let E := StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) m
    let P := Finset.univ \ {c}
    StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (tag a).2 = false) =
          B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} ∧
      StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (tag a).2 = true) = ∅ := by
  classical
  dsimp only
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let F0 := lpReplicaCurrentCopies G sites m tag false false
  let F1 := lpReplicaCurrentCopies G sites m tag true false
  let T0 := lpReplicaCurrentCopies G sites m tag false true
  let T1 := lpReplicaCurrentCopies G sites m tag true true
  have hFdis : Disjoint F0 F1 := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    simp only [F0, F1, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha0 ha1
    exact Bool.false_ne_true ((congrArg Prod.fst ha0).symm.trans
      (congrArg Prod.fst ha1))
  have hTdis : Disjoint T0 T1 := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    simp only [T0, T1, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha0 ha1
    exact Bool.false_ne_true ((congrArg Prod.fst ha0).symm.trans
      (congrArg Prod.fst ha1))
  have hfalseSet : (Finset.univ \ {c}).filter
      (fun a => (tag a).2 = false) = (F0 ∪ F1) \ {c} := by
    ext a
    rcases htag : tag a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [F0, F1, lpReplicaCurrentCopies, htag]
  have htrueSet : (Finset.univ \ {c}).filter
      (fun a => (tag a).2 = true) = T0 ∪ T1 := by
    ext a
    by_cases hac : a = c
    · subst a
      rcases htag : tag c with ⟨row, current⟩
      cases row <;> cases current <;>
        simp_all [T0, T1, lpReplicaCurrentCopies]
    · rcases htag : tag a with ⟨row, current⟩
      cases row <;> cases current <;>
        simp [T0, T1, lpReplicaCurrentCopies, htag, hac]
  have hcF : c ∈ F0 ∪ F1 := by
    rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp_all [F0, F1, lpReplicaCurrentCopies]
  constructor
  · rw [hfalseSet,
      StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by
        simpa only [Finset.singleton_subset_iff] using hcF),
      StatMech.GrahamGHS.FourColor.sources_union_of_disjoint hFdis,
      hgate.1, hgate.2.2.2.1]
    simp

  · rw [htrueSet,
      StatMech.GrahamGHS.FourColor.sources_union_of_disjoint hTdis,
      hgate.2.1, hgate.2.2.2.2.1]
    simp


theorem lpReplicaOffdiagDecoratedSource_rank_five_active_card
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    (K.card = 3 ∧
        (Finset.univ \ K).card = 2 ∧
        StatMech.Sharpness.RandomCurrent.sources
          (StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) z.1.1.1)
          (Finset.univ \ K) = ∅) ∨
      K = Finset.univ := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hKsource : StatMech.Sharpness.RandomCurrent.sources E K = B :=
    d.2.2.2.2.1
  have hKlower : 3 ≤ K.card := by
    have hbound := card_randomCurrent_sources_le_two_mul_card E K
    rw [hKsource, card_lpReplica_offdiagSource sites hsite hij] at hbound
    omega
  have hKupper : K.card ≤ 5 := by
    calc
      K.card ≤ Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1) := Finset.card_le_univ _
      _ = 5 := hcopyCard
  have hfullSource : StatMech.Sharpness.RandomCurrent.sources E Finset.univ =
      B := by
    have h := lpReplicaRowGate_fullSources G sites z.1.1.1 ∅ B d.1 d.2
    calc
      StatMech.Sharpness.RandomCurrent.sources E Finset.univ = ∅ ∆ B := by
        simpa only [E] using h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hcompSource : StatMech.Sharpness.RandomCurrent.sources E
      (Finset.univ \ K) = ∅ := by
    rw [StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset
      (Finset.subset_univ K), hfullSource, hKsource]
    ext x
    simp [Finset.mem_symmDiff]
  have hKneFour : K.card ≠ 4 := by
    intro hfour
    have hcompCard : (Finset.univ \ K).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
        Finset.card_univ, hcopyCard, hfour]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcompCard
    rw [hc] at hcompSource
    exact (randomCurrent_sources_singleton_nonempty_of_edgeCopy
      G sites z.1.1.1 c).ne_empty hcompSource
  by_cases hthree : K.card = 3
  · left
    refine ⟨hthree, ?_, hcompSource⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hthree]
  · have hfive : K.card = 5 := by omega
    right
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ K)
    rw [Finset.card_univ, hcopyCard, hfive]


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ) :
    ∀ c, (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (true, false) := by
  intro c
  have hc : c ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false := by
    rw [hsat]
    simp
  simpa only [lpReplicaCurrentCopies, Finset.mem_filter, Finset.mem_univ,
    true_and] using hc


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      Finset.univ := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  have hall := lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies
    G sites hsite hij q hcard z hsat
  ext x
  simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
    Finset.mem_univ, true_and]
  let c := (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2).symm x
  have hc : d.1 c = (true, false) := hall c
  have htag := lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
    G sites i j q z
  have hc' := congrFun htag c
  rw [hc] at hc'
  simpa only [lpReplicaOffdiagDecoratedSourceSlotState,
    lpReplicaOrientedFourColorSlotState,
    lpReplicaOrbitFourColorSlotStateOfTag, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply, iff_true] using congrArg Prod.fst hc'


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_eq_of_crossTrace_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsatZ : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (hsatW : lpReplicaCurrentCopies G sites w.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q w).1 true false =
        Finset.univ)
    (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) : z = w := by
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq]
  exact ⟨htrace,
    (lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
      G sites hsite hij q hcard z hsatZ).trans
      (lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
        G sites hsite hij q hcard w hsatW).symm⟩


theorem lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    ∀ c ∈ Finset.univ \ K, ∀ e ∈ Finset.univ \ K,
      d.1 c = d.1 e := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hCcard : C.card = 2 := by
    have hKcard : K.card = 3 := by
      simpa only [K, d] using hthree
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hKcard]
  intro c hc e he
  change c ∈ C at hc
  change e ∈ C at he
  by_contra htag
  have hce : c ≠ e := by
    intro h
    exact htag (congrArg d.1 h)
  have hCeq : C = {c, e} := by
    obtain ⟨x, y, hxy, hCxy⟩ := Finset.card_eq_two.mp hCcard
    have hcxy : c = x ∨ c = y := by
      rw [hCxy] at hc
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
    have hexy : e = x ∨ e = y := by
      rw [hCxy] at he
      simpa only [Finset.mem_insert, Finset.mem_singleton] using he
    rcases hcxy with rfl | rfl <;> rcases hexy with rfl | rfl
    · exact False.elim (hce rfl)
    · simpa only [hCxy]
    · simpa only [hCxy, Finset.pair_comm]
    · exact False.elim (hce rfl)
  rcases hdc : d.1 c with ⟨row, current⟩
  let F := lpReplicaCurrentCopies G sites z.1.1.1 d.1 row current
  have hcF : c ∈ F := by
    simp only [F, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and, hdc]
  have hneActive : (row, current) ≠ (true, false) := by
    intro hactive
    have hcK : c ∈ K := by
      simp only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hdc.trans hactive
    exact (Finset.mem_sdiff.mp hc).2 hcK
  have hFsub : F ⊆ C := by
    intro a ha
    have hatag : d.1 a = (row, current) := by
      simpa only [F, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using ha
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ a, ?_⟩
    intro haK
    have haActive : d.1 a = (true, false) := by
      simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using haK
    exact hneActive (hatag.symm.trans haActive)
  have heNotF : e ∉ F := by
    intro heF
    have hetag : d.1 e = (row, current) := by
      simpa only [F, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using heF
    exact htag (hdc.trans hetag.symm)
  have hF : F = {c} := by
    ext a
    constructor
    · intro ha
      have haC := hFsub ha
      rw [hCeq] at haC
      simp only [Finset.mem_insert, Finset.mem_singleton] at haC
      rcases haC with rfl | rfl
      · simp
      · exact False.elim (heNotF ha)
    · intro ha
      simp only [Finset.mem_singleton] at ha
      subst a
      exact hcF
  have hFsource : StatMech.Sharpness.RandomCurrent.sources E F = ∅ := by
    cases row <;> cases current
    · simpa only [E, F] using d.2.1
    · simpa only [E, F] using d.2.2.1
    · exact False.elim (hneActive rfl)
    · simpa only [E, F] using d.2.2.2.2.2.1
  rw [hF] at hFsource
  exact (randomCurrent_sources_singleton_nonempty_of_edgeCopy
    G sites z.1.1.1 c).ne_empty hFsource


theorem lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    ∀ c ∈ Finset.univ \ K, ∀ e ∈ Finset.univ \ K,
      c.1.1 = e.1.1 := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hKcard : K.card = 3 := by
    simpa only [K, d] using hthree
  have hCcard : C.card = 2 := by
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hKcard]
  have hCsource : StatMech.Sharpness.RandomCurrent.sources E C = ∅ := by
    have hsplit := lpReplicaOffdiagDecoratedSource_rank_five_active_card
      G sites hsite hij q hcard z
    dsimp only at hsplit
    rcases hsplit with hsmall | hfull
    · simpa only [E, C, K, d] using hsmall.2.2
    · have hfull' : K = Finset.univ := by
        simpa only [K, d] using hfull
      have : K.card = 5 := by
        rw [hfull', Finset.card_univ, hcopyCard]
      omega
  intro c hc e he
  change c ∈ C at hc
  change e ∈ C at he
  by_cases hce : c = e
  · exact congrArg (fun a => a.1.1) hce
  have hCeq : C = {c, e} := by
    obtain ⟨x, y, hxy, hCxy⟩ := Finset.card_eq_two.mp hCcard
    have hcxy : c = x ∨ c = y := by
      rw [hCxy] at hc
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
    have hexy : e = x ∨ e = y := by
      rw [hCxy] at he
      simpa only [Finset.mem_insert, Finset.mem_singleton] using he
    rcases hcxy with rfl | rfl <;> rcases hexy with rfl | rfl
    · exact False.elim (hce rfl)
    · simpa only [hCxy]
    · simpa only [hCxy, Finset.pair_comm]
    · exact False.elim (hce rfl)
  have hpairSource : StatMech.Sharpness.RandomCurrent.sources E {c, e} = ∅ := by
    rw [← hCeq]
    exact hCsource
  have hdisjoint : Disjoint ({c} : Finset _) {e} := by
    simp [hce]
  have hsingleSymm :
      StatMech.Sharpness.RandomCurrent.sources E {c} ∆
        StatMech.Sharpness.RandomCurrent.sources E {e} = ∅ := by
    calc
      _ = StatMech.Sharpness.RandomCurrent.sources E ({c} ∪ {e}) :=
        (StatMech.GrahamGHS.FourColor.sources_union_of_disjoint
          hdisjoint).symm
      _ = StatMech.Sharpness.RandomCurrent.sources E {c, e} := by
        congr 2
      _ = ∅ := hpairSource
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} =
      StatMech.Sharpness.RandomCurrent.sources E {e} :=
    Finset.symmDiff_eq_empty.mp hsingleSymm
  have hfin : (E c).toFinset = (E e).toFinset := by
    rw [← randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag
        E c,
      ← randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag E e]
    · exact hsingle
    · exact StatMech.Sharpness.FluxEdgeCopy.endsM_not_isDiag
        (lpReplicaCurrentGraph G sites) z.1.1.1 e
    · exact StatMech.Sharpness.FluxEdgeCopy.endsM_not_isDiag
        (lpReplicaCurrentGraph G sites) z.1.1.1 c
  have hedge : E c = E e := by
    apply Sym2.ext
    intro x
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hfin]
  simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hedge


theorem lpReplicaOffdiagDecoratedSource_rank_five_complement_is_tagClass
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    ∃ row current, (row, current) ≠ (true, false) ∧
      lpReplicaCurrentCopies G sites z.1.1.1 d.1 row current =
        Finset.univ \ K := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hKcard : K.card = 3 := by
    simpa only [K, d] using hthree
  have hCcard : C.card = 2 := by
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hKcard]
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hCnonempty
  rcases hdc : d.1 c with ⟨row, current⟩
  refine ⟨row, current, ?_, ?_⟩
  · intro hactive
    have hcK : c ∈ K := by
      simp only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hdc.trans hactive
    exact (Finset.mem_sdiff.mp hc).2 hcK
  · apply Finset.Subset.antisymm
    · intro a ha
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have haActive : d.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      have haTag : d.1 a = (row, current) := by
        simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      exact (show (row, current) ≠ (true, false) from
        fun h => (Finset.mem_sdiff.mp hc).2 (by
          simp only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact hdc.trans h)) (haTag.symm.trans haActive)
    · intro a ha
      have hconst :=
        lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
          G sites hsite hij q hcard z hthree a ha c hc
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hconst.trans hdc

set_option maxHeartbeats 1500000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaCurrentCopies G sites z.1.1.1
          (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
          true false) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  have hconst : ∀ a ∈ C, d.1 a = d.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hnoTrueTrue (a) : d.1 a ≠ (true, true) := by
    intro ha
    have haNotK : a ∉ K := by
      intro haK
      have haActive : d.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      exact Bool.false_ne_true
        (congrArg Prod.snd (haActive.symm.trans ha))
    have haC : a ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haNotK⟩
    have h := hconst a haC
    rw [ha, hctag] at h
    simpa using congrArg Prod.fst h
  have hrow1 : lpReplicaRowCopies G sites z.1.1.1 d.1 true = K := by
    ext a
    rcases ha : d.1 a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaRowCopies, K, lpReplicaCurrentCopies, ha]
    exact False.elim (hnoTrueTrue a ha)
  have hsourceTag :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  change lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 _) = _
  rw [hsourceTag,
    lpReplicaOrbitFourColorSlotRowMask_stateOfTag, hrow1]


theorem lpReplicaOffdiagDecoratedSource_rank_five_rowMask_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)).card = 3 := by
  rw [lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
    G sites hsite hij q hcard z hthree c hcC hctag,
    lpReplicaOrbitCommonSlotsOfCopies, Finset.card_map, hthree]


theorem lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_of_inactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false))
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)
        (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 e) = e.1 := by
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2 e
  have hmask := lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
    G sites hsite hij q hcard z hthree c hcC hctag
  have hslot : slot ∉ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask, mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [slot, Equiv.symm_apply_apply] using
      (Finset.mem_sdiff.mp heC).2
  unfold lpReplicaOffdiagDecoratedSourceCrossTrace
    lpReplicaOrbitFourColorSlotCrossNormalize
  rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem
    G sites q _ state slot hslot]
  exact lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
    G sites q z.1.1.1 z.1.1.2 z.2.2 _ e


theorem lpReplica_threeCopyOffdiag_endpointSupport
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 3)
    (hsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    let E := StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) m
    (K.biUnion fun c => (E c).toFinset) =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let support : Finset (LPReplicaCurrentVertex V) :=
    K.biUnion fun c => (E c).toFinset
  have hsupportCard : support.card ≤ 6 := by
    calc
      support.card ≤ ∑ c ∈ K, (E c).toFinset.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ K, 2 := by
        apply Finset.sum_le_sum
        intro c _
        rw [Sym2.card_toFinset]
        split <;> omega
      _ = 6 := by simp [hKcard]
  have hsubset :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 ⊆ support := by
    rw [← hsource]
    exact randomCurrent_sources_subset_endpointSupport E K
  have hoffdiagCard := card_lpReplica_offdiagSource sites hsite hij
  have heq :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 = support := by
    apply Finset.eq_of_subset_of_card_le hsubset
    omega
  exact heq.symm


theorem lpReplica_threeCopyOffdiag_edge_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 3)
    (hsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    Set.InjOn (fun c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m => c.1.1) K := by
  classical
  intro c hc e he hedge
  by_contra hce
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let R := K.erase c
  have heR : e ∈ R := Finset.mem_erase.mpr ⟨Ne.symm hce, he⟩
  have hEcEe : E c = E e := by
    simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hedge
  have hsupportSub : (K.biUnion fun a => (E a).toFinset) ⊆
      R.biUnion fun a => (E a).toFinset := by
    intro x hx
    obtain ⟨a, haK, hxa⟩ := Finset.mem_biUnion.mp hx
    by_cases hac : a = c
    · subst a
      apply Finset.mem_biUnion.mpr
      exact ⟨e, heR, by simpa only [hEcEe] using hxa⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨a, Finset.mem_erase.mpr ⟨hac, haK⟩, hxa⟩
  have hRcard : R.card = 2 := by
    change (K.erase c).card = 2
    rw [Finset.card_erase_of_mem hc, hKcard]
  have hsupportCard : (K.biUnion fun a => (E a).toFinset).card ≤ 4 := by
    calc
      _ ≤ (R.biUnion fun a => (E a).toFinset).card :=
        Finset.card_le_card hsupportSub
      _ ≤ ∑ a ∈ R, (E a).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ R, 2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [Sym2.card_toFinset]
        split <;> omega
      _ = 4 := by simp [hRcard]
  have hsupport := lpReplica_threeCopyOffdiag_endpointSupport
    G sites hsite hij m K hKcard hsource
  have hBcard := card_lpReplica_offdiagSource sites hsite hij
  dsimp only at hsupport
  rw [hsupport, hBcard] at hsupportCard
  omega


theorem lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_injOn_active
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c0 : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc0C : c0 ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc0tag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c0 =
      (false, false)) :
    Set.InjOn (lpReplicaOrbitFourColorSlotEdge G sites q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z))
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaCurrentCopies G sites z.1.1.1
          (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
          true false)) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  have hmask : lpReplicaOrbitFourColorSlotRowMask G sites q state =
      lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 K :=
    lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hKsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    exact d.2.2.2.2.1
  have hrawInj := lpReplica_threeCopyOffdiag_edge_injective
    G sites hsite hij z.1.1.1 K (by simpa only [K, d] using hthree) hKsource
  intro x hx y hy hedge
  let cx := E.symm x
  let cy := E.symm y
  have hcxK : cx ∈ K := by
    exact (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
      G sites q z.1.1.1 z.1.1.2 z.2.2 K x).mp hx
  have hcyK : cy ∈ K := by
    exact (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
      G sites q z.1.1.1 z.1.1.2 z.2.2 K y).mp hy
  have hxmask : x ∈ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask]
    exact hx
  have hymask : y ∈ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask]
    exact hy
  have hstateEdge (a : LPReplicaOrbitCommonSlot G sites q) :
      lpReplicaOrbitFourColorSlotEdge G sites q state a = (E.symm a).1 := by
    let ca := E.symm a
    have h := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
      G sites q z.1.1.1 z.1.1.2 z.2.2
        (lpReplicaOrientedFourColorTag G sites ∅
          (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q
          (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
            (lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
                lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
                lpMatchingGhostSource
                  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                  lpReplicaCurrentGhost1) q z)) ca
    simpa only [state, lpReplicaOffdiagDecoratedSourceSlotState,
      lpReplicaOrientedFourColorSlotState, ca, E,
      Equiv.apply_symm_apply] using h
  have hxnorm := lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
    G sites q (lpReplicaOrbitFourColorSlotRowMask G sites q state)
      state x hxmask
  have hynorm := lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
    G sites q (lpReplicaOrbitFourColorSlotRowMask G sites q state)
      state y hymask
  have hreflect : lpReplicaCurrentEdgeReflect G sites cx.1 =
      lpReplicaCurrentEdgeReflect G sites cy.1 := by
    calc
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) x := by
        simpa only [lpReplicaOffdiagDecoratedSourceCrossTrace,
          lpReplicaOrbitFourColorSlotCrossNormalize, state, cx,
          hstateEdge] using hxnorm.symm
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) y := hedge
      _ = _ := by
        simpa only [lpReplicaOffdiagDecoratedSourceCrossTrace,
          lpReplicaOrbitFourColorSlotCrossNormalize, state, cy,
          hstateEdge] using hynorm
  have hedgeFin : cx.1 = cy.1 :=
    (lpReplicaCurrentEdgeReflect_involutive G sites).injective hreflect
  have hcxy : cx = cy := hrawInj hcxK hcyK
    (congrArg Subtype.val hedgeFin)
  exact E.symm.injective hcxy

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_inactivePair_mem_eligible
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c0 : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc0C : c0 ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc0tag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c0 =
      (false, false)) :
    Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∈
      lpReplicaEligibleInactivePairs
        (lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let M := lpReplicaOrbitFourColorSlotRowMask G sites q state
  let C := Finset.univ \ M
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  have hM : M = lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 K := by
    exact lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hMcard : M.card = 3 := by
    exact lpReplicaOffdiagDecoratedSource_rank_five_rowMask_card_eq_three
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hCcard : C.card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ M),
      Finset.card_univ, hcard, hMcard]
  have hactive :=
    lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_injOn_active
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hsame :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree
  have hinactive (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∈ C) :
      E.symm x ∈ Finset.univ \ K := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hxK
    have hxM : x ∈ M := by
      rw [hM, mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      simpa only [E, Equiv.symm_apply_apply] using hxK
    exact (Finset.mem_sdiff.mp hx).2 hxM
  have hedge (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∈ C) :
      lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) x =
        (E.symm x).1 := by
    simpa only [E, Equiv.apply_symm_apply] using
      (lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_of_inactive
        G sites hsite hij q hcard z hthree (c := c0) (e := E.symm x)
          hc0C hc0tag
          (hinactive x hx))
  simp only [lpReplicaEligibleInactivePairs, Finset.mem_filter,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  change C.card = 2 ∧ _
  refine ⟨hCcard, ?_, ?_⟩
  · have hdouble : Finset.univ \ C = M := by
      ext x
      simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    rw [hdouble, hM]
    exact hactive
  · intro x hx y hy
    rw [hedge x hx, hedge y hy]
    exact Subtype.ext
      (hsame (E.symm x) (hinactive x hx) (E.symm y) (hinactive y hy))

end
end StatMech.Ising
