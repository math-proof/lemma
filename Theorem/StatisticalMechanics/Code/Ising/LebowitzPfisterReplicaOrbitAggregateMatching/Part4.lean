/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem nonempty_lpReplicaAggregateCrossToggleMatching_iff_hall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaAggregateCrossToggleMatching G sites q) <->
      LPReplicaAggregateCrossToggleHall G sites q := by
  classical
  constructor
  · rintro ⟨m⟩
    unfold LPReplicaAggregateCrossToggleHall
    apply (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaAggregateCrossToggleNeighbors G sites q)).mpr
    refine ⟨m.output, m.output_injective, ?_⟩
    intro z
    simp only [lpReplicaAggregateCrossToggleNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact m.output_related z
  · intro hHall
    have hHall' : forall S : Finset
        (LPReplicaAggregateDecoratedSource G sites q),
        S.card <= (S.biUnion
          (lpReplicaAggregateCrossToggleNeighbors G sites q)).card := by
      simpa only [LPReplicaAggregateCrossToggleHall] using hHall
    obtain ⟨move, hmove, hmem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (lpReplicaAggregateCrossToggleNeighbors G sites q)).mp hHall'
    refine ⟨{
      output := move
      output_injective := hmove
      output_related := ?_
    }⟩
    intro z
    have hz := hmem z
    simpa only [lpReplicaAggregateCrossToggleNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and] using hz


theorem lpReplicaAggregateDecoratedInjection_of_crossToggleMatching
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : LPReplicaAggregateCrossToggleMatching G sites q) :
    LPReplicaAggregateDecoratedInjection G sites q :=
  ⟨m.output, m.output_injective⟩


theorem lpReplicaAggregateProfileOrbitInequality_of_aggregateCrossToggleHall
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregateCrossToggleHall G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  have hm :=
    (nonempty_lpReplicaAggregateCrossToggleMatching_iff_hall
      G sites q).mpr (hHall q)
  exact lpReplicaAggregateDecoratedInjection_of_crossToggleMatching
    G sites q (Classical.choice hm)


end
end StatMech.Ising
