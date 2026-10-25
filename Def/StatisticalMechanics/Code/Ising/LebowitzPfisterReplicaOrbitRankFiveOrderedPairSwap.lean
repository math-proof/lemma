/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagDecoratedSourceSwap
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedSource G sites i j q ≃
      LPReplicaOffdiagDecoratedSource G sites j i q :=
  Equiv.cast (congrArg
    (fun B => LPReplicaDecoratedOrbitAtom G sites ∅ B q)
    (lpReplicaOffdiagSourceBoundary_swap sites i j))


noncomputable def lpReplicaAggregateDecoratedSourceSwap
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
  LPReplicaAggregateDecoratedSource G sites q := by
  have hij := lpReplicaAggregateDecoratedSource_indices_ne G sites q z
  exact ⟨z.2.1, z.1,
    ⟨z.2.2.1.1, by simpa [hij, hij.symm] using z.2.2.1.2⟩,
    lpReplicaOffdiagDecoratedSourceSwap
      G sites z.1 z.2.1 q z.2.2.2⟩

end
end StatMech.Ising
