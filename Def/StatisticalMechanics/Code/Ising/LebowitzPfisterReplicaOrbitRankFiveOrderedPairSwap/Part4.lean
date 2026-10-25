/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateDecoratedSourcePairEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaAggregateDecoratedSource G sites q ≃
      Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative
        G sites q where
  toFun := lpReplicaAggregateDecoratedSourcePairCode G sites q
  invFun := lpReplicaAggregateDecoratedSourcePairDecode G sites q
  left_inv := lpReplicaAggregateDecoratedSourcePairDecode_code G sites q
  right_inv := lpReplicaAggregateDecoratedSourcePairCode_decode G sites q

end
end StatMech.Ising
