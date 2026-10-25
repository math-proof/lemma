/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part6
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

theorem compEulerWalk_cov (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f : V) :
    ∀ e ∈ (compF F f).edgeSet, e ∈ (compEulerWalk F hF hev f).edges :=
  (compF_eulerCircuit F hF hev f).choose_spec

theorem compEulerWalk_edges_toFinset (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f : V) :
    ((compEulerWalk F hF hev f).edges.toFinset : Finset (Sym2 V))
      = F.filter (fun e => ∀ x ∈ e, (subgraphF F).Reachable f x) := by
  ext e
  rw [List.mem_toFinset, Finset.mem_filter]
  constructor
  · intro he
    have hadj : e ∈ (compF F f).edgeSet := (compEulerWalk F hF hev f).edges_subset_edgeSet he
    rw [mem_compF_edgeSet F hF f e] at hadj
    exact hadj
  · intro ⟨hmem, hreach⟩
    have : e ∈ (compF F f).edgeSet := by rw [mem_compF_edgeSet F hF f e]; exact ⟨hmem, hreach⟩
    exact compEulerWalk_cov F hF hev f e this


section ComponentIndex

variable {V : Type} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

open SimpleGraph (ConnectedComponent)


theorem edge_reachable_from_out (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    {x y : V} (hmem : s(x, y) ∈ F) :
    ∀ z ∈ s(x, y), (subgraphF F).Reachable ((subgraphF F).connectedComponentMk x).out z := by
  intro z hz
  have hadj : (subgraphF F).Adj x y := by
    rw [subgraphF_adj]; exact ⟨hmem, by intro h; subst h; exact hF _ hmem (by rw [Sym2.mk_isDiag_iff])⟩
  have hrxy : (subgraphF F).Reachable x y := hadj.reachable
  
  have hox : (subgraphF F).Reachable ((subgraphF F).connectedComponentMk x).out x := by
    have := ((subgraphF F).connectedComponentMk x).out_eq
    exact ConnectedComponent.exact this
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hox
  · exact hox.trans hrxy

theorem evenSubgraph_decomp (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) :
    ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V)
      (W : (i : ι) → (subgraphF F).Walk (w i) (w i)),
      F = s.biUnion (fun i => (W i).edges.toFinset) ∧
      (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) := by
  classical
  refine ⟨(subgraphF F).ConnectedComponent, inferInstance, Finset.univ,
    fun c => c.out,
    fun c => (compEulerWalk F hF hev c.out).mapLe (compF_le F c.out), ?_, ?_⟩
  · 
    ext e
    rw [Finset.mem_biUnion]
    constructor
    · intro he
      induction e with
      | h x y =>
        refine ⟨(subgraphF F).connectedComponentMk x, Finset.mem_univ _, ?_⟩
        simp only
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_toFinset]
        
        have hcov := compEulerWalk_cov F hF hev ((subgraphF F).connectedComponentMk x).out
        apply hcov
        rw [mem_compF_edgeSet F hF _ s(x,y)]
        exact ⟨he, edge_reachable_from_out F hF he⟩
    · rintro ⟨c, _, hc⟩
      simp only at hc
      rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_toFinset] at hc
      have : e ∈ (compF F c.out).edgeSet :=
        (compEulerWalk F hF hev c.out).edges_subset_edgeSet hc
      rw [mem_compF_edgeSet F hF c.out e] at this
      exact this.1
  · 
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro e hec hed
    simp only at hec hed
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_toFinset] at hec hed
    have hcc : e ∈ (compF F c.out).edgeSet :=
      (compEulerWalk F hF hev c.out).edges_subset_edgeSet hec
    have hdd : e ∈ (compF F d.out).edgeSet :=
      (compEulerWalk F hF hev d.out).edges_subset_edgeSet hed
    rw [mem_compF_edgeSet F hF c.out e] at hcc
    rw [mem_compF_edgeSet F hF d.out e] at hdd
    
    revert hcc hdd
    induction e with
    | h x y =>
      intro hcc hdd
      have hcx : (subgraphF F).Reachable c.out x := hcc.2 x (by rw [Sym2.mem_iff]; left; rfl)
      have hdx : (subgraphF F).Reachable d.out x := hdd.2 x (by rw [Sym2.mem_iff]; left; rfl)
      have : c = d := by
        have h1 : (subgraphF F).connectedComponentMk c.out
            = (subgraphF F).connectedComponentMk x := ConnectedComponent.sound hcx
        have h2 : (subgraphF F).connectedComponentMk d.out
            = (subgraphF F).connectedComponentMk x := ConnectedComponent.sound hdx
        have hco : (subgraphF F).connectedComponentMk c.out = c := c.out_eq
        have hdo : (subgraphF F).connectedComponentMk d.out = d := d.out_eq
        rw [hco] at h1; rw [hdo] at h2; rw [h1, ← h2]
      exact hcd this


theorem subgraphF_le_of_subset {Gd : SimpleGraph V} [DecidableRel Gd.Adj]
    {F : Finset (Sym2 V)} (hFsub : F ⊆ Gd.edgeFinset) : subgraphF F ≤ Gd := by
  intro a b hab
  rw [subgraphF_adj] at hab
  have : s(a,b) ∈ Gd.edgeFinset := hFsub hab.1
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
  exact this


theorem evenSubgraphs_no_diag {Gd : SimpleGraph V} [DecidableRel Gd.Adj]
    {F : Finset (Sym2 V)} (hFsub : F ⊆ Gd.edgeFinset) (e : Sym2 V) (he : e ∈ F) : ¬ e.IsDiag := by
  have : e ∈ Gd.edgeFinset := hFsub he
  rw [SimpleGraph.mem_edgeFinset] at this
  exact Gd.not_isDiag_of_mem_edgeSet this


theorem edges_mapLe_toFinset {G H : SimpleGraph V} (h : G ≤ H) {a b : V} (p : G.Walk a b) :
    (p.mapLe h).edges.toFinset = p.edges.toFinset := by
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]


theorem evenSubgraphWalkDecomp_general (Gd : SimpleGraph V) [DecidableRel Gd.Adj] :
    EvenSubgraphWalkDecomp Gd := by
  classical
  intro F hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hF
  obtain ⟨hFsub, hFev⟩ := hF
  have hF_no_diag : ∀ e ∈ F, ¬ e.IsDiag := fun e he => evenSubgraphs_no_diag hFsub e he
  obtain ⟨ι, hιdec, s, w, W, hcov, hdisj⟩ := evenSubgraph_decomp F hF_no_diag hFev
  have hle : subgraphF F ≤ Gd := subgraphF_le_of_subset hFsub
  have hbu : s.biUnion (fun i => (W i).edges.toFinset)
      = s.biUnion (fun i => ((W i).mapLe hle).edges.toFinset) := by
    apply Finset.biUnion_congr rfl
    intro i _
    exact (edges_mapLe_toFinset hle (W i)).symm
  refine ⟨ι, hιdec, s, w, fun i => (W i).mapLe hle, ?_, ?_⟩
  · exact hcov.trans hbu
  · intro i hi j hj hij
    have hd := hdisj hi hj hij
    simp only [Function.onFun]
    rw [edges_mapLe_toFinset hle (W i), edges_mapLe_toFinset hle (W j)]
    exact hd

end ComponentIndex
end EvenSubgraphDecomp
end Ising
end StatMech
