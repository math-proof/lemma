/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part7
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.Part2


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def
    lpReplicaAggregateRankFiveCombinedEmbeddingOfNonstrictKeyFibers
    {S : Type*} [Fintype S]
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hfiber : forall target,
      Fintype.card {s : S // key s = target} <= 2)
    (hnonstrict : forall s,
      ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q ⟨0, key s⟩) :
    S ⊕ LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  let handled := lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers
    G sites q key hfiber
  apply lpReplicaAggregateRankFiveCombinedEmbeddingOfNonstrictEmbedding
    G sites hsite q hcard handled
  intro s
  exact lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers_not_strict
    G sites q key hfiber hnonstrict s

end
end StatMech.Ising
