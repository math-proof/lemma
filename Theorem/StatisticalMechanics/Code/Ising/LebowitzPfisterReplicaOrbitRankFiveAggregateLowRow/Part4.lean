/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1600000 in


theorem lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z w : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u)) (hzw : z ≠ w)
    (hout : lpReplicaLowRowCrossTraceOutput
      G sites hsite hij q hcard u z =
        lpReplicaLowRowCrossTraceOutput
          G sites hsite hij q hcard u w) :
    Nonempty (LPReplicaLowRowCollisionParallelData G sites i j q z.1) := by
  classical
  have hzmem := Finset.mem_filter.mp z.2
  have hwmem := Finset.mem_filter.mp w.2
  have hzsource := hzmem.1
  have hwsource := hwmem.1
  have hzlow := hzmem.2
  have hwlow := hwmem.2
  have htracez := (Finset.mem_filter.mp hzsource).2
  have htracew := (Finset.mem_filter.mp hwsource).2
  let dz := lpReplicaLowRowMarkedOutputData
    G sites hsite hij q hcard z.1 hzlow
  let dw := lpReplicaLowRowMarkedOutputData
    G sites hsite hij q hcard w.1 hwlow
  have hout' : dz.output = dw.output := congrArg Subtype.val hout
  let sz := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z.1
  let sw := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w.1
  let Mz := lpReplicaOrbitFourColorSlotRowMask G sites q sz
  let Mw := lpReplicaOrbitFourColorSlotRowMask G sites q sw
  let Ez := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1.1
    z.1.1.1.2 z.1.2.2
  let Ew := lpReplicaProfileCopyEquivCommonSlot G sites q w.1.1.1.1
    w.1.1.1.2 w.1.2.2
  let az := Ez dz.copy
  let aw := Ew dw.copy
  have hsinglez : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1.1
      z.1.1.1.2 z.1.2.2 {dz.copy} = {az} := by
    simp [lpReplicaOrbitCommonSlotsOfCopies, az, Ez]
  have hsinglew : lpReplicaOrbitCommonSlotsOfCopies G sites q w.1.1.1.1
      w.1.1.1.2 w.1.2.2 {dw.copy} = {aw} := by
    simp [lpReplicaOrbitCommonSlotsOfCopies, aw, Ew]
  have hazM : az ∈ Mz := by
    change az ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z.1)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z.1 hzlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [az, Ez, Equiv.symm_apply_apply] using dz.copy_active
  have hawM : aw ∈ Mw := by
    change aw ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w.1)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard w.1 hwlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [aw, Ew, Equiv.symm_apply_apply] using dw.copy_active
  have htargetState :
      lpReplicaOrbitFourColorSlotCrossToggle G sites q {az} sz =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q {aw} sw := by
    calc
      _ = (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q dz.output).2 := by
        simpa only [sz, hsinglez] using dz.state_eq.symm
      _ = (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q dw.output).2 := congrArg
        (fun y => (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2) hout'
      _ = _ := by simpa only [sw, hsinglew] using dw.state_eq
  have hmask : Mz ∆ {az} = Mw ∆ {aw} := by
    have h := congrArg (lpReplicaOrbitFourColorSlotRowMask G sites q)
      htargetState
    simpa only [lpReplicaOrbitFourColorSlotRowMask_crossToggle, Mz, Mw]
      using h
  have hzwVal : z.1 ≠ w.1 := fun h => hzw (Subtype.ext h)
  have hazaw : az ≠ aw := by
    intro h
    have ht : lpReplicaOrbitFourColorSlotCrossToggle G sites q {az} sz =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q {az} sw := by
      simpa only [h] using htargetState
    have hstate : sz = sw :=
      (lpReplicaOrbitFourColorSlotCrossToggle_involutive
        G sites q {az}).injective ht
    exact hzwVal (lpReplicaOffdiagDecoratedSourceSlotState_injective
      G sites i j q hstate)
  have hawNotMz : aw ∉ Mz := by
    intro hawMz
    have hawLeft : aw ∈ Mz ∆ {az} := by
      simp [Finset.mem_symmDiff, hawMz, hazaw.symm]
    rw [hmask] at hawLeft
    simp [Finset.mem_symmDiff, hawM] at hawLeft
  let e := Ez.symm aw
  let Kz := lpReplicaCurrentCopies G sites z.1.1.1.1
    (lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1 true false
  let Cz := Finset.univ \ Kz
  have heC : e ∈ Cz := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heK
    have hawMz : aw ∈ Mz := by
      change aw ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z.1)
      rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
        G sites hsite hij q hcard z.1 hzlow]
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      simpa only [e, Ez, Equiv.apply_symm_apply] using heK
    exact hawNotMz hawMz
  have hrawCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr Ez
      _ = 5 := hcard
  have hCcard : Cz.card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Kz),
      Finset.card_univ, hrawCard]
    change 5 - (lpReplicaCurrentCopies G sites z.1.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1
        true false).card = 2
    rw [hzlow.1]
  have hexists : ∃ f ∈ Cz, f ≠ e :=
    Finset.exists_mem_ne (s := Cz) (by omega) e
  let f := Classical.choose hexists
  have hfC : f ∈ Cz := (Classical.choose_spec hexists).1
  have hfe : f ≠ e := (Classical.choose_spec hexists).2
  have hcur :
      (lpReplicaRowTagEquivFin4.symm
        (sz.color ⟨aw, Finset.mem_univ _⟩)).2 =
      (lpReplicaRowTagEquivFin4.symm
        (sw.color ⟨aw, Finset.mem_univ _⟩)).2 := by
    calc
      _ = (lpReplicaRowTagEquivFin4.symm
          ((lpReplicaOrbitFourColorSlotCrossToggle
            G sites q {az} sz).color ⟨aw, Finset.mem_univ _⟩)).2 :=
        (lpReplicaOrbitFourColorSlotCrossToggle_current
          G sites q {az} sz aw).symm
      _ = (lpReplicaRowTagEquivFin4.symm
          ((lpReplicaOrbitFourColorSlotCrossToggle
            G sites q {aw} sw).color ⟨aw, Finset.mem_univ _⟩)).2 := by
        rw [htargetState]
      _ = _ := lpReplicaOrbitFourColorSlotCrossToggle_current
        G sites q {aw} sw aw
  have hwtag : (lpReplicaDecoratedSourceRowGateData
      G sites i j q w.1).1 dw.copy = (true, false) := by
    simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using dw.copy_active
  have hecurrent :
      ((lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1 e).2 =
        false := by
    calc
      _ = (lpReplicaRowTagEquivFin4.symm
          (sz.color ⟨aw, Finset.mem_univ _⟩)).2 := by
        simpa only [sz, e, Ez, Equiv.apply_symm_apply] using
          (lpReplicaOffdiagDecoratedSourceSlotState_current_copy
            G sites i j q z.1 e).symm
      _ = (lpReplicaRowTagEquivFin4.symm
          (sw.color ⟨aw, Finset.mem_univ _⟩)).2 := hcur
      _ = ((lpReplicaDecoratedSourceRowGateData
          G sites i j q w.1).1 dw.copy).2 := by
        simpa only [sw, aw, Ew] using
          lpReplicaOffdiagDecoratedSourceSlotState_current_copy
            G sites i j q w.1 dw.copy
      _ = false := by rw [hwtag]
  let c0 := Classical.choose hzlow.2
  have hc0C := (Classical.choose_spec hzlow.2).1
  have hc0row := (Classical.choose_spec hzlow.2).2
  have heconst :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z.1 hzlow.1 e heC c0 hc0C
  have herow :
      ((lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1 e).1 =
        false := (congrArg Prod.fst heconst).trans hc0row
  have hetag : (lpReplicaDecoratedSourceRowGateData
      G sites i j q z.1).1 e = (false, false) := by
    exact Prod.ext herow hecurrent
  have hftag : (lpReplicaDecoratedSourceRowGateData
      G sites i j q z.1).1 f = (false, false) := by
    rw [lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z.1 hzlow.1 f hfC e heC, hetag]
  have heTraceEdge : lpReplicaOrbitFourColorSlotEdge G sites q u aw = e.1 := by
    calc
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace
            G sites i j q z.1) aw := congrArg
        (fun s => lpReplicaOrbitFourColorSlotEdge G sites q s aw)
          htracez |>.symm
      _ = e.1 := by
        simpa only [e, Ez, Equiv.apply_symm_apply] using
          lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive
            G sites hsite hij q hcard z.1 hzlow e heC
  have hwSourceEdge : lpReplicaOrbitFourColorSlotEdge G sites q sw aw =
      dw.copy.1 := by
    simpa only [sw, aw, Ew] using
      lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy G sites q
        w.1.1.1.1 w.1.1.1.2 w.1.2.2
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
                  lpReplicaCurrentGhost1) q w.1)) dw.copy
  have hwTraceEdge : lpReplicaOrbitFourColorSlotEdge G sites q u aw =
      lpReplicaCurrentEdgeReflect G sites dw.copy.1 := by
    calc
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace
            G sites i j q w.1) aw := congrArg
        (fun s => lpReplicaOrbitFourColorSlotEdge G sites q s aw)
          htracew |>.symm
      _ = _ := by
        unfold lpReplicaOffdiagDecoratedSourceCrossTrace
          lpReplicaOrbitFourColorSlotCrossNormalize
        rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
          G sites q Mw sw aw hawM, hwSourceEdge]
  have hmarked : dz.copy.1.1 = lpReplicaCurrentSeamEdge sites i ∨
      dz.copy.1.1 = lpReplicaCurrentSeamEdge sites j := by
    rcases dz.branch with ⟨_yz, _hyz, hzseam⟩ | ⟨_yz, _hyz, hzseam⟩
    · exact Or.inl hzseam
    · exact Or.inr hzseam
  have heparallel : e.1 = dz.copy.1 := by
    rcases dz.branch with ⟨_yz, hyz, hzseam⟩ | ⟨_yz, hyz, hzseam⟩
    · rcases dw.branch with ⟨_yw, _hyw, hwseam⟩ | ⟨_yw, hyw, _hwseam⟩
      · have hwfixed : dw.copy.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
          lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
            G sites i w.1.1.1.1 dw.copy hwseam
        have hwreflect := (mem_lpReplicaCurrentEdgeOrbitFixed
          G sites dw.copy.1).mp hwfixed
        calc
          e.1 = lpReplicaOrbitFourColorSlotEdge G sites q u aw :=
            heTraceEdge.symm
          _ = lpReplicaCurrentEdgeReflect G sites dw.copy.1 := hwTraceEdge
          _ = dw.copy.1 := hwreflect.symm
          _ = dz.copy.1 := Subtype.ext (hwseam.trans hzseam.symm)
      · rw [hyz, hyw] at hout'
        cases hout'
    · rcases dw.branch with ⟨_yw, hyw, _hwseam⟩ | ⟨_yw, _hyw, hwseam⟩
      · rw [hyz, hyw] at hout'
        cases hout'
      · have hwfixed : dw.copy.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
          lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
            G sites j w.1.1.1.1 dw.copy hwseam
        have hwreflect := (mem_lpReplicaCurrentEdgeOrbitFixed
          G sites dw.copy.1).mp hwfixed
        calc
          e.1 = lpReplicaOrbitFourColorSlotEdge G sites q u aw :=
            heTraceEdge.symm
          _ = lpReplicaCurrentEdgeReflect G sites dw.copy.1 := hwTraceEdge
          _ = dw.copy.1 := hwreflect.symm
          _ = dz.copy.1 := Subtype.ext (hwseam.trans hzseam.symm)
  have hfparallel : f.1.1 = dz.copy.1.1 :=
    (lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z.1 hzlow.1 f hfC e heC).trans
        (congrArg Subtype.val heparallel)
  exact ⟨{
    activeCopy := dz.copy
    inactiveCopy₀ := e
    inactiveCopy₁ := f
    active_mem := dz.copy_active
    inactive₀_mem := heC
    inactive₁_mem := hfC
    inactive₀_parallel := congrArg Subtype.val heparallel
    inactive₁_parallel := hfparallel
    inactive₀_tag := hetag
    inactive₁_tag := hftag
    inactive_ne := hfe.symm
    markedSeam := hmarked }⟩


end
end StatMech.Ising
