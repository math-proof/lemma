/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hz : z ∈ lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
      G sites i j q) :
    LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
      G sites i j q z := by
  classical
  have hz' : z ∈ Finset.univ \
      lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q := by
    simpa only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive] using hz
  have hnot := (Finset.mem_sdiff.mp hz').2
  rcases LPReplicaOffdiagDecoratedSource.low_or_resolvable_or_unmarkedSaturated_rankFive
      G sites hsite hij q hcard z with hlow | hresolve | hunmarked
  · exfalso
    apply hnot
    apply Finset.mem_union_left
    simp [lpReplicaOffdiagLowRowSourcesRankFive, hlow]
  · exfalso
    apply hnot
    apply Finset.mem_union_right
    simp [lpReplicaOffdiagResolvableHighRowSourcesRankFive, hresolve]
  · exact hunmarked


theorem lpReplicaAggregateDecoratedSourceSelectedSeam_ne_left_of_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (hz : LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
      G sites z.1 z.2.1 q z.2.2.2) :
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z ≠ z.1 := by
  obtain ⟨c, hc⟩ :=
    lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q z
  intro hk
  apply hz.2.1 c
  exact hc.trans (congrArg (lpReplicaCurrentSeamEdge sites) hk)


theorem lpReplicaAggregateDecoratedSourceSelectedSeam_ne_right_of_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (hz : LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
      G sites z.1 z.2.1 q z.2.2.2) :
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z ≠
      z.2.1 := by
  obtain ⟨c, hc⟩ :=
    lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q z
  intro hk
  apply hz.2.2 c
  exact hc.trans (congrArg (lpReplicaCurrentSeamEdge sites) hk)


end
end StatMech.Ising
