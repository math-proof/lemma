/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowMinCut
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowAugPath
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowDecomposition
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowAugPath
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition

open Finset BigOperators Classical

noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure DirectedGraph (V : Type*) [Fintype V] [DecidableEq V] where
  edge : V → V → Prop
  edge_decidable : ∀ u v : V, Decidable (edge u v)
  s : V
  t : V
  s_ne_t : s ≠ t

instance (G : DirectedGraph V) (u v : V) : Decidable (G.edge u v) := G.edge_decidable u v

structure DirPath (G : DirectedGraph V) where
  vertices : List V
  nonempty : vertices ≠ []
  starts_at_s : vertices.head nonempty = G.s
  ends_at_t : vertices.getLast nonempty = G.t
  length_ge_two : vertices.length ≥ 2
  nodup : vertices.Nodup
  edges_valid : ∀ e ∈ vertices.zip vertices.tail, G.edge e.1 e.2

def DirPath.edges {G : DirectedGraph V} (p : DirPath G) : List (V × V) :=
  p.vertices.zip p.vertices.tail

def PairwiseEdgeDisjoint {G : DirectedGraph V} (paths : Fin k → DirPath G) : Prop :=
  ∀ i j : Fin k, i ≠ j →
    ∀ e : V × V, ¬ (e ∈ (paths i).edges ∧ e ∈ (paths j).edges)

structure EdgeDisjointPaths (G : DirectedGraph V) (k : ℕ) where
  paths : Fin k → DirPath G
  disjoint : PairwiseEdgeDisjoint paths

noncomputable def minSTCutSize (G : DirectedGraph V) : ℕ :=
  Finset.inf' (Finset.univ.filter (fun S : Finset V => G.s ∈ S ∧ G.t ∉ S))
    (by
      simp only [Finset.filter_nonempty_iff]
      exact ⟨{G.s}, Finset.mem_univ _, Finset.mem_singleton_self _,
        fun h => G.s_ne_t (Finset.mem_singleton.mp h).symm⟩)
    (fun S => (Finset.univ.filter (fun p : V × V =>
      p.1 ∈ S ∧ p.2 ∈ Sᶜ ∧ G.edge p.1 p.2)).card)

noncomputable def maxEdgeDisjointPaths (G : DirectedGraph V) : ℕ :=
  Finset.sup' (Finset.univ.filter (fun k : Fin (Fintype.card (V × V) + 1) =>
    Nonempty (EdgeDisjointPaths G k.val)))
    (by
      simp only [Finset.filter_nonempty_iff]
      exact ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _,
        ⟨⟨Fin.elim0, fun i j hij => (Fin.elim0 i)⟩⟩⟩)
    (fun k => k.val)

def DirectedGraph.toFlowNetwork (G : DirectedGraph V) : FlowNetwork V where
  cap := fun u v => if G.edge u v then 1 else 0
  s := G.s
  t := G.t
  s_ne_t := G.s_ne_t
  cap_nonneg := fun u v => by split_ifs <;> linarith

def DirectedGraph.removePathEdges (G : DirectedGraph V) (p : DirPath G) :
    DirectedGraph V where
  edge := fun u v => G.edge u v ∧ (u, v) ∉ p.edges
  edge_decidable := fun _ _ => inferInstance
  s := G.s
  t := G.t
  s_ne_t := G.s_ne_t
