/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in


theorem lpReplicaAggregateDecoratedSourceSwap_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Involutive
      (lpReplicaAggregateDecoratedSourceSwap G sites q) := by
  intro z
  rcases z with ⟨i, j, w, atom⟩
  simp only [lpReplicaAggregateDecoratedSourceSwap]
  congr
  have hswap : lpReplicaOffdiagDecoratedSourceSwap G sites j i q =
      (lpReplicaOffdiagDecoratedSourceSwap G sites i j q).symm := by
    unfold lpReplicaOffdiagDecoratedSourceSwap
    rw [← Equiv.cast_symm]
  rw [hswap]
  exact (lpReplicaOffdiagDecoratedSourceSwap
    G sites i j q).symm_apply_apply atom


theorem lpReplicaAggregateDecoratedSourceSwap_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaAggregateDecoratedSourceSwap G sites q) :=
  (lpReplicaAggregateDecoratedSourceSwap_involutive G sites q).injective


theorem lpReplicaAggregateDecoratedSourceSwap_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    lpReplicaAggregateDecoratedSourceSwap G sites q z ≠ z := by
  intro hswap
  have hindices := congrArg Sigma.fst hswap
  exact lpReplicaAggregateDecoratedSource_indices_ne G sites q z hindices.symm


end
end StatMech.Ising
