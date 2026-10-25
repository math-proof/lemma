/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part7
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_rectHorizontalEdges_disjoint_verticalEdges (M N : Nat) :
    Disjoint (ons_rectHorizontalEdges M N) (ons_rectVerticalEdges M N) := by
  rw [Finset.disjoint_left]
  intro edge hhor hver
  rw [ons_rectHorizontalEdges, Finset.mem_map] at hhor
  rw [ons_rectVerticalEdges, Finset.mem_map] at hver
  obtain ⟨⟨i, j⟩, _, rfl⟩ := hhor
  obtain ⟨⟨i', j'⟩, _, h⟩ := hver
  change ons_rectVerticalEdge (i', j') = ons_rectHorizontalEdge (i, j) at h
  rw [ons_rectHorizontalEdge, ons_rectVerticalEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · have hx1 : i'.val = i.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    have hx2 : i'.val = i.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.2
    omega
  · have hx1 : i'.val = i.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    have hx2 : i'.val = i.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.2
    omega

theorem ons_rectDualGraph_edgeFinset_eq (M N : Nat) :
    (ons_rectDualGraph M N).edgeFinset =
      ons_rectHorizontalEdges M N ∪ ons_rectVerticalEdges M N := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change ons_rectDualAdj M N u v ↔ _
      rw [Finset.mem_union]
      constructor
      · rintro (⟨hy, hx⟩ | ⟨hx, hy⟩)
        · by_cases huv : u.1.val < v.1.val
          · have hval : v.1.val = u.1.val + 1 := by
              rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt huv)] at hx
              omega
            let i : Fin M := ⟨u.1.val, by omega⟩
            refine Or.inl ?_
            rw [ons_rectHorizontalEdges, Finset.mem_map]
            refine ⟨(i, u.2), Finset.mem_univ _, ?_⟩
            change ons_rectHorizontalEdge (i, u.2) = s(u, v)
            unfold ons_rectHorizontalEdge
            apply Sym2.eq_iff.mpr
            left
            constructor
            · apply Prod.ext
              · exact Fin.ext (by rfl)
              · rfl
            · apply Prod.ext
              · exact Fin.ext (by simpa using hval.symm)
              · exact hy
          · have hvu : v.1.val < u.1.val := by
              have hne : u.1.val ≠ v.1.val := by
                intro h; simp [h] at hx
              omega
            have hval : u.1.val = v.1.val + 1 := by
              rw [Nat.dist_comm,
                Nat.dist_eq_sub_of_le (Nat.le_of_lt hvu)] at hx
              omega
            let i : Fin M := ⟨v.1.val, by omega⟩
            refine Or.inl ?_
            rw [ons_rectHorizontalEdges, Finset.mem_map]
            refine ⟨(i, v.2), Finset.mem_univ _, ?_⟩
            change ons_rectHorizontalEdge (i, v.2) = s(u, v)
            unfold ons_rectHorizontalEdge
            apply Sym2.eq_iff.mpr
            right
            constructor
            · apply Prod.ext
              · exact Fin.ext (by rfl)
              · rfl
            · apply Prod.ext
              · exact Fin.ext (by simpa using hval.symm)
              · exact hy.symm
        · by_cases huv : u.2.val < v.2.val
          · have hval : v.2.val = u.2.val + 1 := by
              rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt huv)] at hy
              omega
            let j : Fin N := ⟨u.2.val, by omega⟩
            refine Or.inr ?_
            rw [ons_rectVerticalEdges, Finset.mem_map]
            refine ⟨(u.1, j), Finset.mem_univ _, ?_⟩
            change ons_rectVerticalEdge (u.1, j) = s(u, v)
            unfold ons_rectVerticalEdge
            apply Sym2.eq_iff.mpr
            left
            constructor
            · apply Prod.ext
              · rfl
              · exact Fin.ext (by rfl)
            · apply Prod.ext
              · exact hx
              · exact Fin.ext (by simpa using hval.symm)
          · have hvu : v.2.val < u.2.val := by
              have hne : u.2.val ≠ v.2.val := by
                intro h; simp [h] at hy
              omega
            have hval : u.2.val = v.2.val + 1 := by
              rw [Nat.dist_comm,
                Nat.dist_eq_sub_of_le (Nat.le_of_lt hvu)] at hy
              omega
            let j : Fin N := ⟨v.2.val, by omega⟩
            refine Or.inr ?_
            rw [ons_rectVerticalEdges, Finset.mem_map]
            refine ⟨(v.1, j), Finset.mem_univ _, ?_⟩
            change ons_rectVerticalEdge (v.1, j) = s(u, v)
            unfold ons_rectVerticalEdge
            apply Sym2.eq_iff.mpr
            right
            constructor
            · apply Prod.ext
              · rfl
              · exact Fin.ext (by rfl)
            · apply Prod.ext
              · exact hx.symm
              · exact Fin.ext (by simpa using hval.symm)
      · rintro (hhor | hver)
        · rw [ons_rectHorizontalEdges, Finset.mem_map] at hhor
          obtain ⟨⟨i, j⟩, _, h⟩ := hhor
          change ons_rectHorizontalEdge (i, j) = s(u, v) at h
          rw [ons_rectHorizontalEdge, Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [ons_rectDualAdj, Nat.dist_eq_sub_of_le, Nat.dist_comm]
        · rw [ons_rectVerticalEdges, Finset.mem_map] at hver
          obtain ⟨⟨i, j⟩, _, h⟩ := hver
          change ons_rectVerticalEdge (i, j) = s(u, v) at h
          rw [ons_rectVerticalEdge, Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [ons_rectDualAdj, Nat.dist_eq_sub_of_le, Nat.dist_comm]

theorem ons_rectDualGraph_card_edgeFinset (M N : Nat) :
    (ons_rectDualGraph M N).edgeFinset.card =
      M * (N + 1) + (M + 1) * N := by
  rw [ons_rectDualGraph_edgeFinset_eq,
    Finset.card_union_of_disjoint
      (ons_rectHorizontalEdges_disjoint_verticalEdges M N)]
  simp [ons_rectHorizontalEdges, ons_rectVerticalEdges]

theorem ons_rectDualGraph_eq_boxProd_pathGraph (M N : Nat) :
    ons_rectDualGraph M N =
      SimpleGraph.pathGraph (M + 1) □ SimpleGraph.pathGraph (N + 1) := by
  ext u v
  simp only [ons_rectDualGraph, SimpleGraph.boxProd_adj,
    SimpleGraph.pathGraph_adj]
  unfold ons_rectDualAdj
  constructor
  · rintro (⟨hy, hx⟩ | ⟨hx, hy⟩)
    · left
      refine ⟨?_, hy⟩
      by_cases hle : u.1.val ≤ v.1.val
      · rw [Nat.dist_eq_sub_of_le hle] at hx
        omega
      · right
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))] at hx
        omega
    · right
      refine ⟨?_, hx⟩
      by_cases hle : u.2.val ≤ v.2.val
      · rw [Nat.dist_eq_sub_of_le hle] at hy
        omega
      · right
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))] at hy
        omega
  · rintro (⟨huv | hvu, hy⟩ | ⟨huv | hvu, hx⟩)
    · left
      refine ⟨hy, ?_⟩
      rw [Nat.dist_eq_sub_of_le (by omega)]
      omega
    · left
      refine ⟨hy, ?_⟩
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]
      omega
    · right
      refine ⟨hx, ?_⟩
      rw [Nat.dist_eq_sub_of_le (by omega)]
      omega
    · right
      refine ⟨hx, ?_⟩
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]
      omega

theorem ons_rectDualGraph_connected (M N : Nat) :
    (ons_rectDualGraph M N).Connected := by
  rw [ons_rectDualGraph_eq_boxProd_pathGraph]
  exact (SimpleGraph.pathGraph_connected M).boxProd
    (SimpleGraph.pathGraph_connected N)


theorem evenSubgraphs_sdiff_tree_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hT : T.IsAcyclic) :
    Set.InjOn (fun F : Finset (Sym2 V) => F \ T.edgeFinset)
      (evenSubgraphs G : Set (Finset (Sym2 V))) := by
  intro A hA B hB heq
  change A \ T.edgeFinset = B \ T.edgeFinset at heq
  have hAdata : A ⊆ G.edgeFinset ∧ IsEvenSubgraph A := by
    simpa [evenSubgraphs] using hA
  have hBdata : B ⊆ G.edgeFinset ∧ IsEvenSubgraph B := by
    simpa [evenSubgraphs] using hB
  let D := A ∆ B
  have hDeven : IsEvenSubgraph D :=
    isEvenSubgraph_symmDiff hAdata.2 hBdata.2
  have hDsub : D ⊆ T.edgeFinset := by
    intro edge hedge
    rw [Finset.mem_symmDiff] at hedge
    by_contra hedgeT
    rcases hedge with hedge | hedge
    · have hleft : edge ∈ A \ T.edgeFinset :=
        Finset.mem_sdiff.mpr ⟨hedge.1, hedgeT⟩
      rw [heq, Finset.mem_sdiff] at hleft
      exact hedge.2 hleft.1
    · have hright : edge ∈ B \ T.edgeFinset :=
        Finset.mem_sdiff.mpr ⟨hedge.1, hedgeT⟩
      rw [← heq, Finset.mem_sdiff] at hright
      exact hedge.2 hright.1
  have hDempty : D = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨edge, hedge⟩
    have hnoDiag : ∀ e ∈ D, ¬ e.IsDiag := by
      intro e he
      have heT : e ∈ T.edgeSet := by
        rw [← SimpleGraph.mem_edgeFinset]
        exact hDsub he
      exact T.not_isDiag_of_mem_edgeSet heT
    have hle : subgraphF D ≤ T := by
      intro a b hab
      rw [subgraphF_adj] at hab
      have heT : s(a, b) ∈ T.edgeFinset := hDsub hab.1
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heT
      exact heT
    have hac : (subgraphF D).IsAcyclic := hT.anti hle
    have hne : (subgraphF D).edgeSet.Nonempty :=
      ⟨edge, (mem_edgeSet_subgraphF D hnoDiag edge).mpr hedge⟩
    exact (StatMech.Lattice.jvp_not_isAcyclic_of_even_nonempty
      (subgraphF D) (subgraphF_even D hnoDiag hDeven) hne) hac
  ext edge
  have hnot : edge ∉ D := by rw [hDempty]; simp
  change edge ∉ A ∆ B at hnot
  rw [Finset.mem_symmDiff] at hnot
  tauto

theorem card_evenSubgraphs_le_spanningTree_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hT : T.IsAcyclic) :
    (evenSubgraphs G).card ≤ 2 ^ (G.edgeFinset \ T.edgeFinset).card := by
  let restrict := fun F : Finset (Sym2 V) => F \ T.edgeFinset
  have hinj : Set.InjOn restrict
      (evenSubgraphs G : Set (Finset (Sym2 V))) :=
    evenSubgraphs_sdiff_tree_injOn G T hT
  have hsubset : (evenSubgraphs G).image restrict ⊆
      (G.edgeFinset \ T.edgeFinset).powerset := by
    intro F hF
    rw [Finset.mem_image] at hF
    obtain ⟨A, hA, rfl⟩ := hF
    rw [Finset.mem_powerset]
    have hAsub : A ⊆ G.edgeFinset := by
      rw [evenSubgraphs, Finset.mem_filter,
        Finset.mem_powerset] at hA
      exact hA.1
    exact Finset.sdiff_subset_sdiff hAsub (Finset.Subset.rfl)
  calc
    (evenSubgraphs G).card = ((evenSubgraphs G).image restrict).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((G.edgeFinset \ T.edgeFinset).powerset).card :=
      Finset.card_le_card hsubset
    _ = 2 ^ (G.edgeFinset \ T.edgeFinset).card :=
      Finset.card_powerset _

end
end StatMech.Onsager
