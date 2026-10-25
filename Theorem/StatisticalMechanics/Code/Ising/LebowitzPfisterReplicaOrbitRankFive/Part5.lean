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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_iSeam
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inl y)).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
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
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hall (a) : d0.1 a = (true, false) := by
    have ha : a ∈ lpReplicaCurrentCopies G sites m d0.1 true false := by
      rw [hsat]
      exact Finset.mem_univ a
    simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using ha
  have hctag0 : d0.1 c = (true, false) := hall c
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag0]
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Si := by rw [hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hrow1Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true ⊆
        lpReplicaRowCopies G sites m d0.1 true := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha ⊢
    exact congrArg Prod.fst (hall a)
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact d0.2.2.2.2.2.2
      (StatMech.GrahamGHS.FourColor.connK_mono hrow1Sub hconn)
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {c} := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] at ha ⊢
    by_contra hac
    simp only [hac, if_neg] at ha
    exact Bool.false_ne_true (ha.symm.trans (congrArg Prod.fst (hall a)))
  have hsingleDisconn : ¬ StatMech.Sharpness.RandomCurrent.connK E {c}
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    have hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
        lpReplicaCurrentGhost1 := by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
    obtain ⟨a, ha, hg0⟩ := exists_mem_ends_of_connK_of_ne E
      {c} hghost hconn
    have hac : a = c := by simpa only [Finset.mem_singleton] using ha
    subst a
    change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ c.1.1 at hg0
    rw [hc] at hg0
    simp [lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost0] at hg0
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact hsingleDisconn
      (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
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
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hc
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Si Sj T q s c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  refine ⟨lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites i j q s, Or.inl ⟨s, rfl⟩, ?_⟩
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q hfixedD]
  exact hgeneric

set_option maxHeartbeats 600000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagBalancedOutput G sites i j q y ∧
        lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y =
          lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z ∧
        (lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2).card = 4 := by
  classical
  obtain ⟨y, hyBal, hstate⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_iSeam
      G sites q z hsat c hc
  let Y : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl y
  refine ⟨Y, hyBal, ?_, ?_⟩
  · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [hstate]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q _ _
  · let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
      z.1.1.2 z.2.2 c
    have hsourceMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
        G sites hsite hij q hcard z hsat
    change (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q (Sum.inl y)).2).card = 4
    rw [hstate, lpReplicaOrbitFourColorSlotRowMask_crossToggle, hsourceMask]
    have hslots : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c} = {slot} := by
      unfold lpReplicaOrbitCommonSlotsOfCopies
      rw [Finset.map_singleton]
      rfl
    have hdiff : (Finset.univ ∆ ({slot} : Finset
        (LPReplicaOrbitCommonSlot G sites q))) = Finset.univ \ {slot} := by
      ext x
      simp [Finset.mem_symmDiff]
    rw [hslots, hdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard, Finset.card_singleton]


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_half_eq_empty
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (cut : LPReplicaCoupledPairedCut G sites z.1.1.1
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      (lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z).1) :
    cut.half = ∅ := by
  classical
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  have hall (a) : d0.1 a = (true, false) := by
    have ha : a ∈ lpReplicaCurrentCopies G sites z.1.1.1
        d0.1 true false := by
      rw [hsat]
      exact Finset.mem_univ a
    simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using ha
  have hempty : lpReplicaCurrentCopies G sites z.1.1.1
      d.1 true false = ∅ := by
    ext a
    constructor
    · intro ha
      have htag : d.1 a = (true, false) := by
        simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      change lpReplicaSwapRowsTag d0.1 a = (true, false) at htag
      simp [lpReplicaSwapRowsTag, hall a] at htag
    · simp
  apply LPReplicaCoupledPairedCut.half_eq_empty_of_row1False_empty
    G sites z.1.1.1
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      d.1 cut
  simpa only [d, lpReplicaDecoratedSourceSwappedRowGateData] using hempty


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_doubledHalf_eq_empty
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (cut : LPReplicaCoupledPairedCut G sites z.1.1.1
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      (lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z).1) :
    cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
  rw [lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_half_eq_empty
    G sites i j q z hsat cut]
  simp

set_option maxHeartbeats 1200000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    ∃ (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
      (c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1),
      LPReplicaOffdiagBalancedOutput G sites i j q y ∧
        (c.1.1 = lpReplicaCurrentSeamEdge sites i ∨
          c.1.1 = lpReplicaCurrentSeamEdge sites j) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
  rcases lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three
      G sites hsite hij q hcard z hthree with
    ⟨c, hcK, hc⟩ | ⟨c, hcK, hc⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hy, _hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hthree c hcK hc
    exact ⟨Sum.inl y, c, hyBal, Or.inl hc, hy⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hy, _hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hthree c hcK hc
    exact ⟨Sum.inr y, c, hyBal, Or.inr hc, hy⟩


theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_active_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
  classical
  obtain ⟨y, c, hyBal, _, hstate⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three
      G sites hsite hij q hcard z hthree
  refine ⟨y, ?_⟩
  simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
    Finset.mem_filter]
  constructor
  · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hyBal
  · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [hstate]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q _ _


theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_iSeam_parallelPair
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1) (hek : e.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false))
    (hetag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e =
      (false, false))
    (hce : c ≠ e) :
    3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card := by
  classical
  obtain ⟨_s, _hp, _hL, _hP, _hmove, yk, hykBal, hykState,
      _hykPres⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
      G sites hsite hij q hcard z hthree k hkK hk
  obtain ⟨yc, hycBal, hycState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive
      G sites hsite hij q hcard z hthree k c hkK hk hcC hck hctag
  obtain ⟨ye, hyeBal, hyeState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive
      G sites hsite hij q hcard z hthree k e hkK hk heC hek hetag
  let Yk : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl yk
  let Yc : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl yc
  let Ye : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl ye
  have targetMem (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
      (hyBal : LPReplicaOffdiagBalancedOutput G sites i j q y)
      (P : Finset (LPReplicaOrbitCommonSlot G sites q))
      (hstate : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q P
          (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
      y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hyBal
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  have hYk := targetMem Yk hykBal _ hykState
  have hYc := targetMem Yc hycBal _ hycState
  have hYe := targetMem Ye hyeBal _ hyeState
  have hkc : k ≠ c := by
    intro h
    subst c
    exact (Finset.mem_sdiff.mp hcC).2 hkK
  have hke : k ≠ e := by
    intro h
    subst e
    exact (Finset.mem_sdiff.mp heC).2 hkK
  have hYkc : Yk ≠ Yc :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Yc k c hykState hycState hkc
  have hYke : Yk ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Ye k e hykState hyeState hke
  have hYce : Yc ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yc Ye c e hycState hyeState hce
  calc
    3 = ({Yk, Yc, Ye} : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)).card := by
      simp [hYkc, hYke, hYce]
    _ ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card :=
      Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hYk
        · exact hYc
        · exact hYe)
 


theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_jSeam_parallelPair
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites j)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1) (hek : e.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false))
    (hetag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e =
      (false, false))
    (hce : c ≠ e) :
    3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card := by
  classical
  obtain ⟨_s, _hp, _hL, _hP, _hmove, yk, hykBal, hykState,
      _hykPres⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
      G sites hsite hij q hcard z hthree k hkK hk
  obtain ⟨yc, hycBal, hycState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive
      G sites hsite hij q hcard z hthree k c hkK hk hcC hck hctag
  obtain ⟨ye, hyeBal, hyeState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive
      G sites hsite hij q hcard z hthree k e hkK hk heC hek hetag
  let Yk : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr yk
  let Yc : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr yc
  let Ye : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr ye
  have targetMem (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
      (hyBal : LPReplicaOffdiagBalancedOutput G sites i j q y)
      (P : Finset (LPReplicaOrbitCommonSlot G sites q))
      (hstate : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q P
          (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
      y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hyBal
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  have hYk := targetMem Yk hykBal _ hykState
  have hYc := targetMem Yc hycBal _ hycState
  have hYe := targetMem Ye hyeBal _ hyeState
  have hkc : k ≠ c := by
    intro h
    subst c
    exact (Finset.mem_sdiff.mp hcC).2 hkK
  have hke : k ≠ e := by
    intro h
    subst e
    exact (Finset.mem_sdiff.mp heC).2 hkK
  have hYkc : Yk ≠ Yc :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Yc k c hykState hycState hkc
  have hYke : Yk ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Ye k e hykState hyeState hke
  have hYce : Yc ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yc Ye c e hycState hyeState hce
  calc
    3 = ({Yk, Yc, Ye} : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)).card := by
      simp [hYkc, hYke, hYce]
    _ ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card :=
      Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hYk
        · exact hYc
        · exact hYe)


theorem lpReplicaOffdiagOrbitAtomCardInequality_rank_five_of_coupledPairedOutputCard
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (_hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (houtput : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) ≤
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    G sites i j q houtput


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_five
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≤ 5)
    (hfiveOutput : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 →
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) ≤
        (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  have hcases : Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≤ 2 ∨
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3 ∨
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4 ∨
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 := by
    omega
  rcases hcases with hsmall | hthree | hfour | hrankFive
  · exact lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two
      G sites hsite hij q hsmall
  · exact lpReplicaOffdiagOrbitAtomCardInequality_rank_three
      G sites hsite hij q hthree
  · exact lpReplicaOffdiagOrbitAtomCardInequality_rank_four
      G sites hsite hij q hfour
  · exact lpReplicaOffdiagOrbitAtomCardInequality_rank_five_of_coupledPairedOutputCard
      G sites q hrankFive (hfiveOutput hrankFive)

end
end StatMech.Ising
