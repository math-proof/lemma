/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateDecoratedSourceSwap_canonical_of_not
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (h : ¬ LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z) :
    LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q
      (lpReplicaAggregateDecoratedSourceSwap G sites q z) := by
  have hne : ((Fintype.equivFin I) z.1).val ≠
      ((Fintype.equivFin I) z.2.1).val := by
    intro heq
    apply lpReplicaAggregateDecoratedSource_indices_ne G sites q z
    apply (Fintype.equivFin I).injective
    exact Fin.ext heq
  unfold LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair at h ⊢
  simp only [lpReplicaAggregateDecoratedSourceSwap]
  omega

theorem lpReplicaAggregateDecoratedSourceSwap_not_canonical_of_canonical
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (h : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z) :
    ¬ LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q
      (lpReplicaAggregateDecoratedSourceSwap G sites q z) := by
  unfold LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair at h ⊢
  simp only [lpReplicaAggregateDecoratedSourceSwap]
  omega


end
end StatMech.Ising
