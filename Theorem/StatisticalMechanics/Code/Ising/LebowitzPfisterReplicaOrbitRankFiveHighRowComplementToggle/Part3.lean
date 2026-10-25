/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem
    lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode_not_strict
    {S : Type*} (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (bit : S -> Fin 2)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hcode : Function.Injective (fun s => (bit s, key s)))
    (hnonstrict : ∀ s, ¬
      LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q ⟨0, key s⟩) (s : S) :
    ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        (lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode
          G sites q bit key hcode s) := by
  exact hnonstrict s


end
end StatMech.Ising
