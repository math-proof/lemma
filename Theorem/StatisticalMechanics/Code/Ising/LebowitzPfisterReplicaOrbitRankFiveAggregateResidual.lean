/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateRankFiveResidualCapacity_iff_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveResidualCapacity G sites q <->
      Fintype.card (LPReplicaAggregateDecoratedSource G sites q) <=
        Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  let H := Fintype.card
    (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q)
  let U := Fintype.card
    (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
  let T := Fintype.card (LPReplicaAggregateDecoratedTarget G sites q)
  have hhandled : H <= T := by
    simpa only [H, T] using
      card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target
        G sites hsite q hcard
  have hsource :
      Fintype.card (LPReplicaAggregateDecoratedSource G sites q) = H + U := by
    simpa only [H, U] using
      card_lpReplicaAggregateDecoratedSource_rankFive_eq_handled_add_unmarked
        G sites q
  constructor
  · intro hresidual
    have hUH : U + H <= T := by
      apply Nat.add_le_of_le_sub hhandled
      simpa only [LPReplicaAggregateRankFiveResidualCapacity, U, T, H] using
        hresidual
    rw [hsource]
    simpa only [Nat.add_comm] using hUH
  · intro hfull
    have hHU : H + U <= T := by
      rwa [hsource] at hfull
    unfold LPReplicaAggregateRankFiveResidualCapacity
    apply Nat.le_sub_of_add_le
    simpa only [H, U, T, Nat.add_comm] using hHU


end
end StatMech.Ising
