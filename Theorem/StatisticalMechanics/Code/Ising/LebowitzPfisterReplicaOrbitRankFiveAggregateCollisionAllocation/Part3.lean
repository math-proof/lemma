/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaAggregateLowOrResolvableHighSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card
        (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) =
      ∑ i : I, ∑ j : I, if i = j then 0 else
        (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
          G sites i j q).card := by
  classical
  unfold LPReplicaAggregateLowOrResolvableHighSourceRankFive
  change Fintype.card
      (Sigma fun i : I => Sigma fun j : I =>
        Fin (if i = j then 0 else 1) ×
          ↑(lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
            G sites i j q)) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.card_prod, Fintype.card_coe]
  by_cases hij : i = j <;>
    simp [hij, lpReplicaOffdiagLowOrResolvableHighSourcesRankFive]


theorem card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Fintype.card
        (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) ≤
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  rw [card_lpReplicaAggregateLowOrResolvableHighSourceRankFive,
    ← sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simpa only [hij, ↓reduceIte] using
      lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target
        G sites hsite hij q hcard


end
end StatMech.Ising
