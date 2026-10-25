/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateDecoratedSourcePairDecode_code
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    lpReplicaAggregateDecoratedSourcePairDecode G sites q
        (lpReplicaAggregateDecoratedSourcePairCode G sites q z) = z := by
  by_cases h : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z
  · simp [lpReplicaAggregateDecoratedSourcePairCode,
      lpReplicaAggregateDecoratedSourcePairDecode, h]
  · simp [lpReplicaAggregateDecoratedSourcePairCode,
      lpReplicaAggregateDecoratedSourcePairDecode, h,
      lpReplicaAggregateDecoratedSourceSwap_involutive G sites q z]

theorem lpReplicaAggregateDecoratedSourcePairCode_decode
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative
      G sites q) :
    lpReplicaAggregateDecoratedSourcePairCode G sites q
        (lpReplicaAggregateDecoratedSourcePairDecode G sites q x) = x := by
  rcases x with ⟨b, z⟩
  fin_cases b
  · simp [lpReplicaAggregateDecoratedSourcePairDecode,
      lpReplicaAggregateDecoratedSourcePairCode, z.2]
  · have hn :=
      lpReplicaAggregateDecoratedSourceSwap_not_canonical_of_canonical
        G sites q z.1 z.2
    simp [lpReplicaAggregateDecoratedSourcePairDecode,
      lpReplicaAggregateDecoratedSourcePairCode, hn,
      lpReplicaAggregateDecoratedSourceSwap_involutive G sites q z.1]


end
end StatMech.Ising
