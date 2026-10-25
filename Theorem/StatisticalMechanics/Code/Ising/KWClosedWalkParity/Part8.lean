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
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

theorem mem_compSuppF (F : Finset (Sym2 V)) {f g : V} :
    g ∈ compSuppF F f ↔ (subgraphF F).Reachable f g := by
  unfold compSuppF; rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem self_mem_compSuppF (F : Finset (Sym2 V)) (f : V) : f ∈ compSuppF F f := by
  rw [mem_compSuppF]


theorem compF_support_subset (F : Finset (Sym2 V)) (f : V) :
    (compF F f).support ⊆ (compSuppF F f : Set V) := by
  intro a ha
  rw [SimpleGraph.mem_support] at ha
  obtain ⟨b, hadj, hra, _⟩ := ha
  rw [Finset.mem_coe, mem_compSuppF]; exact hra


theorem compF_edge_of_walk_from_base (F : Finset (Sym2 V)) {f g : V}
    (q : (subgraphF F).Walk f g) {e : Sym2 V} (he : e ∈ q.edges) :
    e ∈ (compF F f).edgeSet := by
  induction e with
  | h x y =>
    have hxadj : (subgraphF F).Adj x y := q.adj_of_mem_edges he
    have hx : x ∈ q.support := q.fst_mem_support_of_mem_edges he
    have hy : y ∈ q.support := q.snd_mem_support_of_mem_edges he
    have hrx : (subgraphF F).Reachable f x := ⟨q.takeUntil x hx⟩
    have hry : (subgraphF F).Reachable f y := ⟨q.takeUntil y hy⟩
    rw [SimpleGraph.mem_edgeSet]; exact ⟨hxadj, hrx, hry⟩

theorem compF_reachable_of_reachable (F : Finset (Sym2 V)) {f g : V}
    (h : (subgraphF F).Reachable f g) : (compF F f).Reachable f g := by
  obtain ⟨p⟩ := h
  exact ⟨p.transfer (compF F f) (fun e he => compF_edge_of_walk_from_base F p he)⟩

theorem compF_walk_in_compSuppF (F : Finset (Sym2 V)) {f : V} {g : V}
    (p : (compF F f).Walk f g) : ∀ v ∈ p.support, v ∈ compSuppF F f := by
  intro v hv
  rw [mem_compSuppF]
  have hmem : v ∈ (p.mapLe (compF_le F f)).support := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hv
  exact ⟨(p.mapLe (compF_le F f)).takeUntil v hmem⟩


theorem reachable_induce_of_walk_in_set' {G : SimpleGraph V} {S : Set V}
    {a b : V} (p : G.Walk a b) (hsub : ∀ v ∈ p.support, v ∈ S) (ha : a ∈ S) :
    (G.induce S).Reachable ⟨a, ha⟩ ⟨b, hsub b p.end_mem_support⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy q ih =>
    have hyS : y ∈ S := hsub y (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ q.start_mem_support)
    have hqsub : ∀ v ∈ q.support, v ∈ S := fun v hv =>
      hsub v (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
    have hadjI : (G.induce S).Adj ⟨x, ha⟩ ⟨y, hyS⟩ := by rw [SimpleGraph.induce_adj]; exact hxy
    exact (SimpleGraph.Adj.reachable hadjI).trans (ih hqsub hyS)

theorem compF_induce_connected (F : Finset (Sym2 V)) (f : V) :
    ((compF F f).induce (compSuppF F f : Set V)).Connected := by
  have hself : f ∈ compSuppF F f := self_mem_compSuppF F f
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨f, hself⟩⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a ∈ compSuppF F f := Finset.mem_coe.mp ha
  have hb' : b ∈ compSuppF F f := Finset.mem_coe.mp hb
  rw [mem_compSuppF] at ha' hb'
  obtain ⟨pa⟩ := compF_reachable_of_reachable F ha'
  obtain ⟨pb⟩ := compF_reachable_of_reachable F hb'
  have hp := pa.reverse.append pb
  have hsub : ∀ v ∈ (pa.reverse.append pb).support, v ∈ compSuppF F f := by
    intro v hv
    rw [SimpleGraph.Walk.support_append] at hv
    rcases List.mem_append.mp hv with hva | hvb
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hva
      exact compF_walk_in_compSuppF F pa v hva
    · exact compF_walk_in_compSuppF F pb v (List.mem_of_mem_tail hvb)
  have hrec := reachable_induce_of_walk_in_set' (pa.reverse.append pb) hsub ha
  convert hrec using 2


theorem compF_eulerCircuit (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f : V) :
    ∃ c : (compF F f).Walk f f, ∀ e ∈ (compF F f).edgeSet, e ∈ c.edges := by
  obtain ⟨c, _htrail, hcov⟩ := StatMech.Lattice.EulerianExistence.exists_closed_eulerian_of_finite_support
    (compF F f) (compSuppF F f) (compF_support_subset F f)
    (compF_induce_connected F f) (compF_degree_even F hF hev f)
    (Finset.mem_coe.mpr (self_mem_compSuppF F f))
  exact ⟨c, hcov⟩


theorem mem_compF_edgeSet (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) (f : V) (e : Sym2 V) :
    e ∈ (compF F f).edgeSet ↔ (e ∈ F ∧ ∀ x ∈ e, (subgraphF F).Reachable f x) := by
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · rintro ⟨hadj, hrx, hry⟩
      rw [subgraphF_adj] at hadj
      refine ⟨hadj.1, ?_⟩
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact hrx
      · exact hry
    · rintro ⟨hmem, hreach⟩
      have hxr : (subgraphF F).Reachable f x := hreach x (by rw [Sym2.mem_iff]; left; rfl)
      have hyr : (subgraphF F).Reachable f y := hreach y (by rw [Sym2.mem_iff]; right; rfl)
      have hadj : (subgraphF F).Adj x y := by
        rw [subgraphF_adj]; exact ⟨hmem, by
          intro hxy; subst hxy; exact hF _ hmem (by rw [Sym2.mk_isDiag_iff])⟩
      exact ⟨hadj, hxr, hyr⟩


end EvenSubgraphDecomp
end Ising
end StatMech
