/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
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
  change K.card = 3 /\ exists c, c ∈ C /\ (d.1 c).1 = false at hlow
  obtain ⟨hthree, c, hcC, hcrow⟩ := hlow
  have hconst : ∀ a ∈ C, d.1 a = d.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hrow1 : lpReplicaRowCopies G sites z.1.1.1 d.1 true = K := by
    ext a
    constructor
    · intro ha
      have harow : (d.1 a).1 = true := by
        simpa only [lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra haactive
      have haNotK : a ∉ K := by
        intro haK
        have hatag : d.1 a = (true, false) := by
          simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using haK
        exact haactive hatag
      have haC : a ∈ C := Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, haNotK⟩
      have htag := hconst a haC
      have := congrArg Prod.fst htag
      rw [harow, hcrow] at this
      exact Bool.false_ne_true this.symm
    · intro ha
      have hatag : d.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      simpa only [lpReplicaRowCopies, Finset.mem_filter,
        Finset.mem_univ, true_and, hatag]
  have hsourceTag :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  change lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 _) = _
  rw [hsourceTag, lpReplicaOrbitFourColorSlotRowMask_stateOfTag, hrow1]


theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)).card = 3 := by
  rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
    G sites hsite hij q hcard z hlow,
    lpReplicaOrbitCommonSlotsOfCopies, Finset.card_map]
  exact hlow.1


theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)
        (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 e) = e.1 := by
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2 e
  have hmask :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow
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


theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_injOn_active
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
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
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow
  have hKsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := d.2.2.2.2.1
  have hrawInj := lpReplica_threeCopyOffdiag_edge_injective
    G sites hsite hij z.1.1.1 K hlow.1 hKsource
  intro x hx y hy hedge
  let cx := E.symm x
  let cy := E.symm y
  have hcxK : cx ∈ K :=
    (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
      G sites q z.1.1.1 z.1.1.2 z.2.2 K x).mp hx
  have hcyK : cy ∈ K :=
    (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
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


theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_inactivePair_mem_eligible
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
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
      z.1.1.2 z.2.2 K :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow
  have hMcard : M.card = 3 :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
      G sites hsite hij q hcard z hlow
  have hCcard : C.card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ M),
      Finset.card_univ, hcard, hMcard]
  have hactive :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_injOn_active
      G sites hsite hij q hcard z hlow
  have hsame :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hlow.1
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
      (lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive
        G sites hsite hij q hcard z hlow (E.symm x) (hinactive x hx))
  simp only [lpReplicaEligibleInactivePairs, Finset.mem_filter,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  change C.card = 2 /\ _
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
