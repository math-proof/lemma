/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.Part3


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d).c =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
          G sites hsite q z := by
  exact (Classical.choose_spec
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate
      G sites hsite q hcard z d.1 d.2)).1

theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d).d = d.1 := by
  exact (Classical.choose_spec
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate
      G sites hsite q hcard z d.1 d.2)).2


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    0 < (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).card :=
  Finset.card_pos.mpr
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_nonempty
      G sites hsite q hcard z)

set_option maxHeartbeats 2000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).card ≤ 2 := by
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
  obtain ⟨hKcard, _hsources, _hsupport, hunique⟩ := hpm
  have hg0 := lpReplicaCurrentGhost0_mem_tripleSeamGhostSource
    (V := V) sites a.1 a.2.1 k
  have hg1 := lpReplicaCurrentGhost1_mem_tripleSeamGhostSource
    (V := V) sites a.1 a.2.1 k
  obtain ⟨c0, hc0, _hc0unique⟩ := hunique lpReplicaCurrentGhost0 hg0
  obtain ⟨c1, hc1, _hc1unique⟩ := hunique lpReplicaCurrentGhost1 hg1
  have hc01 : c0 ≠ c1 := by
    intro h
    subst c1
    have he0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ E c0 :=
      Sym2.mem_toFinset.mp hc0.2
    have he1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ E c0 :=
      Sym2.mem_toFinset.mp hc1.2
    have hedge : c0.1.1 =
        s((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
          lpReplicaCurrentGhost1) :=
      sym2_eq_mk_of_mem_of_mem_of_ne he0 he1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])
    have hgraph := SimpleGraph.mem_edgeFinset.mp c0.1.2
    rw [hedge] at hgraph
    simpa [lpReplicaCurrentGraph, lpReplicaCurrentRel,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hgraph
  let ghosts : Finset (Copy (lpReplicaCurrentGraph G sites)
      a.2.2.2.1.1.1) := {c0, c1}
  have hghostsK : ghosts ⊆ K := by
    intro e he
    simp only [ghosts, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hc0.1
    · exact hc1.1
  have hcandidateSub :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z ⊆ K \ ghosts := by
    intro d hd
    have hd' :=
      (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
        G sites hsite q z d).mp hd
    dsimp only at hd'
    apply Finset.mem_sdiff.mpr
    refine ⟨hd'.1, ?_⟩
    simp only [ghosts, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hdc0
      subst d
      exact hd'.2.1 (Sym2.mem_toFinset.mp hc0.2)
    · intro hdc1
      subst d
      exact hd'.2.2.1 (Sym2.mem_toFinset.mp hc1.2)
  calc
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card ≤ (K \ ghosts).card :=
      Finset.card_le_card hcandidateSub
    _ = K.card - ghosts.card := Finset.card_sdiff_of_subset hghostsK
    _ = 2 := by
      have hK : K.card = 4 := hKcard
      have hg : ghosts.card = 2 := by simp [ghosts, hc01]
      rw [hK, hg]


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = 1 ∨
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = 2 := by
  have hpos :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos
      G sites hsite q hcard z
  have hle :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two
      G sites hsite q hcard z
  omega

end
end StatMech.Ising
