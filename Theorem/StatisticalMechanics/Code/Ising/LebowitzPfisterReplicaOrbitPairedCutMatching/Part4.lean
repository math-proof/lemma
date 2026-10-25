/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCoupledPairedHall_of_outputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagCoupledPairedHall G sites i j q := by
  classical
  intro S
  by_cases hS : S = ∅
  · simp [hS]
  let good := lpReplicaOffdiagCoupledPairedOutputs G sites i j q
  have hneighbors (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
      lpReplicaOffdiagCoupledPairedNeighbors G sites i j q z = good := by
    ext y
    simp only [lpReplicaOffdiagCoupledPairedNeighbors, good,
      lpReplicaOffdiagCoupledPairedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact lpReplicaOffdiagCoupledPairedMatch_iff_output G sites i j q z y
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hunion : S.biUnion
      (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q) = good := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨z, hz, hy⟩
      rwa [hneighbors z] at hy
    · intro hy
      obtain ⟨z, hz⟩ := hnonempty
      exact ⟨z, hz, by rwa [hneighbors z]⟩
  rw [hunion]
  calc
    S.card <= Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card (Finset.subset_univ S)
    _ <= good.card := by simpa only [good] using hcard


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  classical
  have hHall := lpReplicaOffdiagCoupledPairedHall_of_outputCard
    G sites i j q hcard
  obtain ⟨move, hmove, _⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q)).mp (by
        simpa only [LPReplicaOffdiagCoupledPairedHall] using hHall)
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
  exact ⟨move, hmove⟩


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedProfileAllocation
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (a : LPReplicaOffdiagCoupledPairedProfileAllocation
      G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    G sites i j q a


theorem lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcard : ∀ q i j, i ≠ j ->
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
        (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_atomCard
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    G sites i j q (hcard q i j hij)


theorem lpReplicaAggregateProfileOrbitInequality_of_coupledPairedProfileAllocations
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (halloc : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    G sites i j q (halloc q i j hij)


theorem lpReplicaMatchingDisconn_le_of_coupledPairedOutputCards
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcard : ∀ q i j, i ≠ j ->
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
        (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  apply lpReplicaMatchingDisconn_le_of_profileOrbit
    G sites beta J hf r hbeta hJ hhf hr
  exact lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards
    G sites beta J hf r hbeta hJ hhf hr hcard


theorem lpReplicaMatchingDisconn_le_of_coupledPairedProfileAllocations
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (halloc : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  apply lpReplicaMatchingDisconn_le_of_coupledPairedOutputCards
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    G sites i j q (halloc q i j hij)


theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_coupledPairedProfileAllocations
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (halloc : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have hmatch :=
    lpReplicaMatchingDisconn_le_of_coupledPairedProfileAllocations
      G sites beta J hf r hbeta hJ hhf hr halloc
  dsimp only at hmatch
  apply (lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])).mpr
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn H beta Jr
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  exact hmatch

end
end StatMech.Ising
