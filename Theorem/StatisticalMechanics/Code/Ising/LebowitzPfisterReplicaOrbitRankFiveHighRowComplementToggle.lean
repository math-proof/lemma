/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in


theorem lpReplicaToggleRows_swapRowsTag_eq_compl
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m P (lpReplicaSwapRowsTag tag) =
      lpReplicaToggleRows G sites m (Finset.univ \ P) tag := by
  funext c
  by_cases hc : c ∈ P
  · rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hc, htag]
  · rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hc, htag]

omit [Fintype I] [DecidableEq I] in

theorem lpReplicaToggleRows_self
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m P
        (lpReplicaToggleRows G sites m P tag) = tag := by
  funext a
  by_cases ha : a ∈ P
  · rcases htag : tag a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, ha, htag]
  · simp [lpReplicaToggleRows, ha]

omit [Fintype I] [DecidableEq I] in


theorem lpReplicaToggleRows_activeSdiff_swapRowsTag_eq_singleton_after_complement
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) (hcK : c ∈ K)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m (K \ {c}) (lpReplicaSwapRowsTag tag) =
      lpReplicaToggleRows G sites m {c}
        (lpReplicaToggleRows G sites m (Finset.univ \ K) tag) := by
  funext a
  by_cases hac : a = c
  · subst a
    rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hcK, htag]
  · by_cases haK : a ∈ K
    · rcases htag : tag a with ⟨row, current⟩
      cases row <;> cases current <;>
        simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hac, haK, htag]
    · rcases htag : tag a with ⟨row, current⟩
      cases row <;> cases current <;>
        simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hac, haK, htag]

omit [Fintype I] [DecidableEq I] in


theorem
    lpReplicaToggleRows_activeSdiff_swapRowsComplementTag_eq_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) (hcK : c ∈ K)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m (K \ {c})
        (lpReplicaSwapRowsTag
          (lpReplicaToggleRows G sites m (Finset.univ \ K) tag)) =
      lpReplicaToggleRows G sites m {c} tag := by
  rw [lpReplicaToggleRows_activeSdiff_swapRowsTag_eq_singleton_after_complement
    G sites m K c hcK]
  rw [lpReplicaToggleRows_self]

omit [Fintype I] [DecidableEq I] in


theorem lpReplicaToggleRows_singleton_after_complement_ne_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) (hcK : c ∈ K)
    (hC : (Finset.univ \ K).Nonempty)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m {c}
        (lpReplicaToggleRows G sites m (Finset.univ \ K) tag) ≠
      lpReplicaToggleRows G sites m {c} tag := by
  obtain ⟨e, heC⟩ := hC
  have heK : e ∉ K := (Finset.mem_sdiff.mp heC).2
  have hec : e ≠ c := by
    intro heq
    exact heK (heq ▸ hcK)
  intro h
  have heq := congrFun h e
  rcases htag : tag e with ⟨row, current⟩
  cases row <;> cases current <;>
    simp [lpReplicaToggleRows, heC, hec, htag] at heq

set_option maxHeartbeats 2000000 in


theorem
    lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_iSeam_complementTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (d.1 r).1 = true)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
    ∃ s : LPReplicaBalancedSelector G sites
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1)
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q,
      s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
        HEq s.selector
          (lpReplicaCurrentCopies G sites z.1.1.1
              (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
              true false \ {c}) ∧
        @HEq
          (Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) s.profile))
          (lpReplicaRowCopies G sites s.profile
            (lpReplicaToggleRows G sites s.profile s.selector s.tag) true)
          (Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1))
          (lpReplicaCurrentCopies G sites z.1.1.1
              (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
              true false \ {c}) ∧
        ∃ y : LPReplicaDecoratedOrbitAtom G sites
            (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q,
          LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
            ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
              G sites i j q (Sum.inl y) ∧
            y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
              G sites i j q s := by
  classical
  dsimp only at hhigh
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites m d0.1 true false
  let C := Finset.univ \ K
  let P := K \ {c}
  let Q := {c} ∪ C
  have hthree : K.card = 3 := by
    simpa only [K, d0] using hhigh.1
  obtain ⟨r, hrC, hrrow⟩ := hhigh.2
  change r ∈ C at hrC
  change (d0.1 r).1 = true at hrrow
  have hctag0 : d0.1 c = (true, false) := by
    simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcK
  have hconst : ∀ a ∈ C, d0.1 a = d0.1 r := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha r hrC
  have hallRow (a) : (d0.1 a).1 = true := by
    by_cases haK : a ∈ K
    · have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      simp [hatag]
    · have haC : a ∈ C :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haK⟩
      exact congrArg Prod.fst (hconst a haC) |>.trans hrrow
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hsourceK : StatMech.Sharpness.RandomCurrent.sources E K = B := by
    simpa only [E, K, B, d0] using d0.2.2.2.2.1
  have hcSub : ({c} : Finset _) ⊆ K := by
    simpa only [Finset.singleton_subset_iff] using hcK
  have hsourceP : StatMech.Sharpness.RandomCurrent.sources E P = Sj ∆ T := by
    calc
      _ = StatMech.Sharpness.RandomCurrent.sources E K ∆
          StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P] using
          StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset hcSub
      _ = B ∆ Si := by rw [hsourceK, hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have hPtag (a) (ha : a ∈ P) : d.1 a = (false, false) := by
    have haK : a ∈ K := (Finset.mem_sdiff.mp ha).1
    have hatag : d0.1 a = (true, false) := by
      simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using haK
    change lpReplicaSwapRowsTag d0.1 a = (false, false)
    simp [lpReplicaSwapRowsTag, hatag]
  have hfilterFalse : P.filter (fun a => (d.1 a).2 = false) = P := by
    ext a
    constructor
    · exact fun ha => (Finset.mem_filter.mp ha).1
    · intro ha
      exact Finset.mem_filter.mpr ⟨ha, by rw [hPtag a ha]⟩
  have hfilterTrue : P.filter (fun a => (d.1 a).2 = true) = ∅ := by
    ext a
    constructor
    · intro ha
      have ha' := Finset.mem_filter.mp ha
      rw [hPtag a ha'.1] at ha'
      simp at ha'
    · intro ha
      simp at ha
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    rw [hfilterFalse]
    exact hsourceP
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    rw [hfilterTrue]
    exact randomCurrent_sources_empty E
  have hcompl : Finset.univ \ P = Q := by
    ext a
    by_cases hac : a = c
    · subst a
      simp [P, Q]
    · by_cases haK : a ∈ K
      · simp [P, Q, C, hac, haK]
      · simp [P, Q, C, hac, haK]
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m Q d0.1 := by
    change lpReplicaToggleRows G sites m P
        (lpReplicaSwapRowsTag d0.1) = _
    rw [lpReplicaToggleRows_swapRowsTag_eq_compl, hcompl]
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true = P := by
    rw [hmove]
    ext a
    by_cases hac : a = c
    · subst a
      simp [P, Q, C, lpReplicaRowCopies, lpReplicaToggleRows, hctag0]
    · by_cases haK : a ∈ K
      · have hatag : d0.1 a = (true, false) := by
          simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using haK
        simp [P, Q, C, lpReplicaRowCopies, lpReplicaToggleRows, hac,
          haK, hatag]
      · simp [P, Q, C, lpReplicaRowCopies, lpReplicaToggleRows, hac,
          haK, hallRow]
  have hrow0Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false = Q := by
    rw [hmove]
    ext a
    by_cases haQ : a ∈ Q
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, haQ, hallRow]
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, haQ, hallRow]
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    apply StatMech.GrahamGHS.FourColor.connK_mono _ hconn
    rw [hrow1Eq]
    intro a ha
    simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hallRow a
  have hCcard : C.card = 2 := by
    have hcopyCard : Fintype.card
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m) = 5 := by
      calc
        _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
          Fintype.card_congr
            (lpReplicaProfileCopyEquivCommonSlot G sites q m
              z.1.1.2 z.2.2)
        _ = 5 := hcard
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hthree]
  obtain ⟨e0, he0C⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    rw [hrow0Eq]
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites i m c e0 C hc hsame
  have huniqueK :=
    lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence
      G sites hsite hij q z hthree
  have huniqueP : ∀ x ∈ P.biUnion (fun f =>
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m f).toFinset),
      ∃! f, f ∈ P ∧
        x ∈ (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m f).toFinset := by
    intro x hx
    obtain ⟨f, hfP, hxf⟩ := Finset.mem_biUnion.mp hx
    refine ⟨f, ⟨hfP, hxf⟩, ?_⟩
    intro g hg
    have hxKsupport : x ∈ K.biUnion (fun b =>
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m b).toFinset) := by
      exact Finset.mem_biUnion.mpr
        ⟨f, (Finset.mem_sdiff.mp hfP).1, hxf⟩
    obtain ⟨_, _, huniq⟩ := huniqueK x hxKsupport
    exact (huniq g ⟨(Finset.mem_sdiff.mp hg.1).1, hg.2⟩).trans
      (huniq f ⟨(Finset.mem_sdiff.mp hfP).1, hxf⟩).symm
  have hnotStrictRaw :
      ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m P :=
    lpReplica_not_strictPhysicalDoubleIncidence_matching
      G sites m P huniqueP
  let s : LPReplicaBalancedSelector G sites B (Sj ∆ T) q := {
    profile := m
    orbit := z.1.1.2
    tag := d.1
    gate := d.2
    orbitLabel := z.2.2
    selector := P
    falseSource := hfalseSource
    trueSource := htrueSource
    row0Disconn := hrow0Disconn
    row1Disconn := hrow1Disconn }
  refine ⟨s, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
  · exact heq_of_eq hrow1Eq
  · let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
      G sites i j q s
    refine ⟨y, Or.inl ⟨s, rfl⟩, ?_, rfl⟩
    rw [LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence]
    rw [lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rw [hrow1Eq]
    exact hnotStrictRaw


@[simp] theorem
    lpReplicaOffdiagDecoratedTargetToAggregate_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q
          (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) ↔
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q y := by
  cases y <;> rfl


theorem lpReplicaOffdiagDecoratedTargetToAggregate_ne_strictRouteCandidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
    (hy : ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites i j q y)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y ≠
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z d := by
  intro hcollision
  apply hy
  apply
    (lpReplicaOffdiagDecoratedTargetToAggregate_hasStrictPhysicalDoubleIncidence
      G sites i j q y).mp
  rw [hcollision]
  exact
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence
      G sites hsite q hcard z d


end
end StatMech.Ising
