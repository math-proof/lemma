/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites j) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inr y)).2 =
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
  have hcends : E c = s(lpReplicaCurrentLeft sites j,
      lpReplicaCurrentRight sites j) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
    simpa only [Sj, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Sj := by rw [hsingle]
      _ = Si ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T
        rw [symmDiff_comm Si Sj, symmDiff_assoc Sj Si T,
          symmDiff_symmDiff_self']
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
    simp only [hac] at ha
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
  let s : LPReplicaBalancedSelector G sites B (Si ∆ T) q := {
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
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hc
  let s' : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q := {
    profile := s.profile
    orbit := s.orbit
    tag := s.tag
    gate := by
      rw [symmDiff_comm Sj Si]
      exact s.gate
    orbitLabel := s.orbitLabel
    selector := s.selector
    falseSource := s.falseSource
    trueSource := s.trueSource
    row0Disconn := s.row0Disconn
    row1Disconn := s.row1Disconn }
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Sj Si T q s' c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
  let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites j i q s'
  refine ⟨y, Or.inr ⟨s', rfl⟩, ?_⟩
  change (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q
    (Sum.inl y)).2 = _
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold y lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
    ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q hfixedD]
  exact hgeneric


end
end StatMech.Ising
