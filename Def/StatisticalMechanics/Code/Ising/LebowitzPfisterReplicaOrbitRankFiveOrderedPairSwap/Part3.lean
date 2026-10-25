/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateDecoratedSourcePairCode
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative
      G sites q := by
  classical
  exact if h : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z then
      ⟨0, ⟨z, h⟩⟩
    else
      ⟨1, ⟨lpReplicaAggregateDecoratedSourceSwap G sites q z,
        lpReplicaAggregateDecoratedSourceSwap_canonical_of_not
          G sites q z h⟩⟩


noncomputable def lpReplicaAggregateDecoratedSourcePairDecode
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative G sites q ->
      LPReplicaAggregateDecoratedSource G sites q
  | ⟨b, z⟩ => if b.1 = 0 then z.1 else
      lpReplicaAggregateDecoratedSourceSwap G sites q z.1

end
end StatMech.Ising
