/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part7
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.Part2


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers_not_strict
    {S : Type*} [Fintype S]
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hfiber : forall target,
      Fintype.card {s : S // key s = target} <= 2)
    (hnonstrict : forall s,
      ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q ⟨0, key s⟩) (s : S) :
    ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        (lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers
          G sites q key hfiber s) := by
  exact lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode_not_strict
    G sites q (finiteFiberMultiplicityCode key hfiber) key
      (finiteFiberMultiplicityCode_key_injective key hfiber)
      hnonstrict s


end
end StatMech.Ising
