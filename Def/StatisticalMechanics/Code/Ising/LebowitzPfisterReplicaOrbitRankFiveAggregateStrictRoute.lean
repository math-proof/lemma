/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTarget
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteData
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    LPReplicaAggregateRankFiveStrictRouteData G sites q a k := by
  dsimp only
  exact Classical.choice
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute_disconnected
      G sites hsite q hcard z)


noncomputable def lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    LPReplicaAggregateDecoratedTarget G sites q := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let route :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteData
      G sites hsite q hcard z
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hdc : route.d ≠ route.c := by
    exact (Finset.mem_sdiff.mp route.hdK).2 ∘ Finset.mem_singleton.mpr
  let l := lpReplicaThirdOfThree a.1 a.2.1 k route.u route.v
  let atom := lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom
    G sites hsite hij hik hjk route.hu route.hv route.huv q a.2.2.2
      route.c route.d route.hc hdc.symm route.hfold route.hdisc
  exact ⟨0, ⟨k, ⟨l, atom⟩⟩⟩

end
end StatMech.Ising
