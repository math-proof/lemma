/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part5
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLowRankSwitching
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_five
    G sites hsite hij q (by omega)
  intro hfive
  omega


theorem lpReplicaAggregateDecoratedInjection_of_commonSlotCard_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4) :
    LPReplicaAggregateDecoratedInjection G sites q := by
  classical
  let Si : I -> Finset (LPReplicaCurrentVertex V) := fun i =>
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let a : I -> I -> Nat := fun i j =>
    Fintype.card (LPReplicaDecoratedOrbitAtom G sites
      (Si i) (Si j ∆ T) q)
  have hterm (i j : I) :
      (if i = j then 0 else
        Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q)) <=
        a i j + a j i := by
    by_cases hij : i = j
    · rw [if_pos hij]
      omega
    · rw [if_neg hij]
      have hcard :=
        lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_four
          G sites hsite hij q hle
      dsimp only [LPReplicaOffdiagOrbitAtomCardInequality] at hcard
      rw [← card_lpReplicaDecoratedOrbitAtom,
        ← card_lpReplicaDecoratedOrbitAtom,
        ← card_lpReplicaDecoratedOrbitAtom] at hcard
      simpa only [LPReplicaOffdiagDecoratedSource, Si, T, a] using hcard
  have hcard :
      Fintype.card (LPReplicaAggregateDecoratedSource G sites q) <=
        Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
    rw [card_lpReplicaAggregateDecoratedSource,
      card_lpReplicaAggregateDecoratedTarget]
    calc
      (∑ i : I, ∑ j : I, if i = j then 0 else
          Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q)) <=
        ∑ i : I, ∑ j : I, (a i j + a j i) := by
          exact Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => hterm i j
      _ = ∑ i : I, ∑ j : I, 2 * a i j := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_comm]
        omega
      _ = ∑ i : I, ∑ j : I, 2 * Fintype.card
          (LPReplicaDecoratedOrbitAtom G sites
            (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q) := by
        rfl
  obtain ⟨move⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨move, move.injective⟩


end
end StatMech.Ising
