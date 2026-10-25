/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.Part2


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem
    mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1) :
    d ∈ lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z ↔
      let a := z.toAggregate G sites q
      let c :=
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
          G sites hsite q z
      d ∈ Finset.univ \ {c} ∧
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
          endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
          endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag := by
  classical
  simp only [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates,
    Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxHeartbeats 2000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_nonempty
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).Nonempty := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  have hc : c.1.1 = lpReplicaCurrentSeamEdge sites k :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
      G sites hsite q z
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z c hc
  dsimp only at hpm
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  obtain ⟨hKcard, _hsources, hsupport, hunique⟩ := hpm
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hunmarked :=
    LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
      G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2
  obtain ⟨d, hdK, hd0, hd1, hddiag⟩ :=
    lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute
      G sites hsite hij hik hjk a.2.2.2.1.1.1 K hKcard hsupport hunique
        (fun e _ => hunmarked.2.1 e) (fun e _ => hunmarked.2.2 e)
  refine ⟨d, ?_⟩
  rw [mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff]
  exact ⟨hdK, hd0, hd1, hddiag⟩

set_option maxHeartbeats 2000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1)
    (hd : d ∈
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    ∃ route : LPReplicaAggregateRankFiveStrictRouteData G sites q a k,
      route.c =
          lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
            G sites hsite q z ∧
        route.d = d := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  have hc : c.1.1 = lpReplicaCurrentSeamEdge sites k :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
      G sites hsite q z
  have hd' :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z d).mp hd
  dsimp only at hd'
  obtain ⟨hdK, hd0, hd1, hddiag⟩ := hd'
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z c hc
  dsimp only at hpm
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  obtain ⟨_hKcard, _hsources, hsupport, hunique⟩ := hpm
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  obtain ⟨u, v, hu, hv, huv, hfold⟩ :=
    lpReplica_strictPhysicalRoute_folded_labels G sites hsite
      hij hik hjk a.2.2.2.1.1.1 K hsupport d hdK hd0 hd1 hddiag
  have hl := lpReplicaThirdOfThree_spec hij hik hjk hu hv huv
  have hdisc :=
    lpReplica_partialReflect_strictMatchingRoute_ghost_disconnected
      G sites hsite a.2.2.2.1.1.1 K
        (lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k) d hdK
        hsupport hunique
        (lpReplicaCurrentGhost0_mem_tripleSeamGhostSource
          sites a.1 a.2.1 k)
        (lpReplicaCurrentGhost1_mem_tripleSeamGhostSource
          sites a.1 a.2.1 k)
        huv hfold
  refine ⟨{
    c := c
    d := d
    u := u
    v := v
    hc := hc
    hdK := hdK
    hu := hu
    hv := hv
    huv := huv
    hfold := hfold
    hl := hl
    hdisc := hdisc
  }, rfl, rfl⟩


end
end StatMech.Ising
