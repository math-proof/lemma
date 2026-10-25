/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hresolve : LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
      G sites i j q z) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
  classical
  rcases hresolve.1 with hsat | hthree
  · rcases hresolve.2 hsat with ⟨c, hc⟩ | ⟨c, hc⟩
    · obtain ⟨y, hyBal, hyTrace, _⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam
          G sites hsite hij q hcard z hsat c hc
      refine ⟨y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hyBal, hyTrace⟩
    · obtain ⟨y, hyBal, hstate⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam
          G sites q z hsat c hc
      refine ⟨Sum.inr y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨hyBal, ?_⟩
      unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  · exact
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_active_card_eq_three
        G sites hsite hij q hcard z hthree.1


end
end StatMech.Ising
