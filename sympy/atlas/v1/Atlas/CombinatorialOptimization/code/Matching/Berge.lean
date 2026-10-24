/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace Walk

def IsAlternatingFrom {u v : V} (p : G.Walk u v) (M : G.Subgraph) : Prop :=
  ∀ (i : ℕ) (hi : i < p.edges.length),
    (Even i → p.edges[i] ∉ M.edgeSet) ∧
    (Odd i → p.edges[i] ∈ M.edgeSet)

def IsAugmentingPath {u v : V} (p : G.Walk u v) (M : G.Subgraph) : Prop :=
  p.IsPath ∧
  u ≠ v ∧
  u ∉ M.verts ∧
  v ∉ M.verts ∧
  p.IsAlternatingFrom M

def IsMaxMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

end Subgraph

def HasAugmentingPath (G : SimpleGraph V) (M : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M

noncomputable def symmDiffMatching {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u v : V} (M : G.Subgraph) (p : G.Walk u v) : G.Subgraph where
  verts := M.verts ∪ {w | w ∈ p.support}
  Adj a b := (M.Adj a b ∧ s(a, b) ∉ p.edges.toFinset) ∨
             (G.Adj a b ∧ s(a, b) ∈ p.edges.toFinset ∧ ¬ M.Adj a b)
  adj_sub := by
    intro a b h; rcases h with ⟨h, _⟩ | ⟨h, _, _⟩; exact M.adj_sub h; exact h
  edge_vert := by
    intro a b h; rcases h with ⟨h, _⟩ | ⟨_, hmem, _⟩
    · exact Or.inl (M.edge_vert h)
    · exact Or.inr (Walk.fst_mem_support_of_mem_edges p (List.mem_toFinset.mp hmem))
  symm := by
    intro a b h; rcases h with ⟨h, hn⟩ | ⟨h, hmem, hn⟩
    · left; exact ⟨M.symm h, by rwa [Sym2.eq_swap]⟩
    · right; exact ⟨G.symm h, by rwa [Sym2.eq_swap], fun h' => hn (M.symm h')⟩

noncomputable def matchingSwapEdge {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (Mstar' : G.Subgraph) (u v w : V)
    (hMstar' : Mstar'.IsMatching) (hAdj : Mstar'.Adj u v) (hGvw : G.Adj v w)
    (hw_fresh : w ∉ Mstar'.verts) : G.Subgraph where
  verts := (Mstar'.verts \ {u}) ∪ {w}
  Adj a b :=
    (Mstar'.Adj a b ∧ ¬(a = u ∧ b = v) ∧ ¬(a = v ∧ b = u)) ∨
    (a = v ∧ b = w) ∨ (a = w ∧ b = v)
  adj_sub := by
    intro a b h; rcases h with ⟨h, _, _⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Mstar'.adj_sub h
    · exact hGvw
    · exact hGvw.symm
  edge_vert := by
    intro a b h; rcases h with ⟨hadj, hne1, hne2⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; constructor
      · exact Mstar'.edge_vert hadj
      · intro ha; rw [Set.mem_singleton_iff] at ha; subst ha
        have huniq := (hMstar' (Mstar'.edge_vert hAdj)).choose_spec.2
        exact hne1 ⟨rfl, (huniq b hadj).trans (huniq v hAdj).symm⟩
    · left; constructor
      · exact Mstar'.edge_vert (Mstar'.symm hAdj)
      · intro h; rw [Set.mem_singleton_iff] at h; exact (Mstar'.adj_sub hAdj).ne h.symm
    · right; exact rfl
  symm := by
    intro a b h; rcases h with ⟨hadj, hne1, hne2⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨Mstar'.symm hadj, fun ⟨h1, h2⟩ => hne2 ⟨h2, h1⟩, fun ⟨h1, h2⟩ => hne1 ⟨h2, h1⟩⟩
    · right; right; exact ⟨rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl⟩
