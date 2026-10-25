/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLowRankSwitching
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateProfileOrbitInequalityAt_of_commonSlotCard_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4) :
    LPReplicaAggregateProfileOrbitInequalityAt G sites beta J hf r q := by
  classical
  let Si : I -> Finset (LPReplicaCurrentVertex V) := fun i =>
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let o := lpReplicaProfileOrbitMass G sites beta J hf r
  have hpoint (i j : I) (hij : i ≠ j) :
      o ∅ (Si i ∆ Si j ∆ T) q <=
        o (Si i) (Si j ∆ T) q + o (Si j) (Si i ∆ T) q := by
    exact lpReplicaProfileOrbitMass_le_add_of_card_atoms
      G sites beta J hf r hbeta hJ hhf hr
      ∅ (Si i ∆ Si j ∆ T) (Si i) (Si j ∆ T)
        (Si j) (Si i ∆ T) q
      (lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_four
        G sites hsite hij q hle)
  have hterm (i j : I) :
      (if i = j then 0 else o ∅ (Si i ∆ Si j ∆ T) q) <=
        o (Si i) (Si j ∆ T) q + o (Si j) (Si i ∆ T) q := by
    by_cases hij : i = j
    · rw [if_pos hij]
      exact add_nonneg
        (lpReplicaProfileOrbitMass_nonneg
          G sites beta J hf r hbeta hJ hhf hr (Si i) (Si j ∆ T) q)
        (lpReplicaProfileOrbitMass_nonneg
          G sites beta J hf r hbeta hJ hhf hr (Si j) (Si i ∆ T) q)
    · rw [if_neg hij]
      exact hpoint i j hij
  dsimp only [LPReplicaAggregateProfileOrbitInequalityAt]
  calc
    (∑ i : I, ∑ j : I, if i = j then 0 else
        o ∅ (Si i ∆ Si j ∆ T) q) <=
      ∑ i : I, ∑ j : I,
        (o (Si i) (Si j ∆ T) q + o (Si j) (Si i ∆ T) q) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = ∑ i : I, ∑ j : I, 2 * o (Si i) (Si j ∆ T) q := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      ring


theorem lpReplicaAggregateProfileOrbitInequality_of_highRankAtomCard
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hhigh : forall q i j, i ≠ j ->
      5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) ->
      LPReplicaOffdiagOrbitAtomCardInequality G sites i j q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_atomCard
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  by_cases hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4
  · exact lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_four
      G sites hsite hij q hle
  · exact hhigh q i j hij (by omega)


theorem lpReplicaAggregateProfileOrbitInequality_of_highRankAggregateInjection
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hhigh : forall q,
      5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) ->
      LPReplicaAggregateDecoratedInjection G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  by_cases hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4
  · exact lpReplicaAggregateDecoratedInjection_of_commonSlotCard_le_four
      G sites hsite q hle
  · exact hhigh q (by omega)


theorem lpReplicaMatchingDisconn_le_of_highRankAtomCard
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hhigh : forall q i j, i ≠ j ->
      5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) ->
      LPReplicaOffdiagOrbitAtomCardInequality G sites i j q) :
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
  exact lpReplicaAggregateProfileOrbitInequality_of_highRankAtomCard
    G sites hsite beta J hf r hbeta hJ hhf hr hhigh


theorem lpReplicaMatchingDisconn_le_of_highRankAggregateInjection
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hhigh : forall q,
      5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) ->
      LPReplicaAggregateDecoratedInjection G sites q) :
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
  exact lpReplicaAggregateProfileOrbitInequality_of_highRankAggregateInjection
    G sites hsite beta J hf r hbeta hJ hhf hr hhigh


theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_highRankAggregateInjection
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hhigh : forall q,
      5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) ->
      LPReplicaAggregateDecoratedInjection G sites q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have hmatch := lpReplicaMatchingDisconn_le_of_highRankAggregateInjection
    G sites hsite beta J hf r hbeta hJ hhf hr hhigh
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
