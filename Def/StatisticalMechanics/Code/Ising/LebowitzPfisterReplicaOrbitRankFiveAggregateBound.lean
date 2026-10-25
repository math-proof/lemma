/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagRankFiveCrossTraceFiberEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    {z // z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u} ↪ Fin 4 := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four
      G sites hsite hij q hcard u)


noncomputable def lpReplicaAggregateRankFiveSourceKey
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaAggregateSourceCrossTraceFiber G sites q u ->
      I × (I × Fin 4) := fun z =>
  let hij := lpReplicaAggregateDecoratedSource_indices_ne G sites q z.1
  let atom : {a // a ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites z.1.1 z.1.2.1 q u} := ⟨z.1.2.2.2, by
    simp only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact z.2⟩
  (z.1.1, (z.1.2.1,
    lpReplicaOffdiagRankFiveCrossTraceFiberEmbedding
      G sites hsite hij q hcard u atom))

end
end StatMech.Ising
