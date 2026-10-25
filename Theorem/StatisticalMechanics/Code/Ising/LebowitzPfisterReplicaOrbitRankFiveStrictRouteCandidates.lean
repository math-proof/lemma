/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (c : Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites
      (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
        (z.toAggregate G sites q))) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    let K := Finset.univ \ {c}
    let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
    K.card = 4 ∧
      StatMech.Sharpness.RandomCurrent.sources E K =
        lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
      K.biUnion (fun e => (E e).toFinset) =
        lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
      ∀ x ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k,
        ∃! e, e ∈ K ∧ x ∈ (E e).toFinset := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hKcard : K.card = 4 :=
    lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive
      G sites q hcard a.2.2.2 c
  have hsources : StatMech.Sharpness.RandomCurrent.sources E K =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy
      G sites q a.2.2.2 c hc
  have htight :
      (StatMech.Sharpness.RandomCurrent.sources E K).card =
        2 * K.card := by
    rw [hsources, card_lpReplicaTripleSeamGhostSource sites hsite
      hij hik hjk, hKcard]
  have hsupport : K.biUnion (fun e => (E e).toFinset) =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    (randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul
      E K htight).trans hsources
  refine ⟨hKcard, hsources, hsupport, ?_⟩
  intro x hx
  apply randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul
    E K htight
  rw [hsupport]
  exact hx


end
end StatMech.Ising
