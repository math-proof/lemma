/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.Part3


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateProfileOrbitInequality_rankFive_of_residualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hresidual : forall q,
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 ->
        LPReplicaAggregateRankFiveResidualCapacity G sites q)
    (hrank : forall q,
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≠ 5 ->
        LPReplicaAggregateDecoratedInjection G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  by_cases hcard : Fintype.card
      (LPReplicaOrbitCommonSlot G sites q) = 5
  · let e := lpReplicaAggregateRankFiveEmbedding_of_residualCapacity
      G sites hsite q hcard (hresidual q hcard)
    exact ⟨e, e.injective⟩
  · exact hrank q hcard

end
end StatMech.Ising
