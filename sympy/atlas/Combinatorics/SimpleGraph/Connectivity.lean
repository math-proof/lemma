/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

/--
Two walks are internally disjoint if they share no vertices other than their endpoints.
-/
def InternallyDisjoint {u v x y : V} (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

/--
We say a graph is infinitely connected if any two vertices are connected by infinitely many
pairwise disjoint paths. Note that graphs with at most one vertex are not classed as
infinitely connected.
-/
def InfinitelyConnected (G : SimpleGraph V) : Prop := Nontrivial V ∧
  Pairwise fun u v ↦ ∃ P : Set (G.Walk u v),
    P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/-!
### Deciding reachability by breadth-first search

This section provides efficient decidability instances for reachability and (pre)connectedness of
finite graphs through a breadth-first search (BFS) algorithm.

The algorithm is as follows: we maintain a finset of visited vertices which we grow with all its
neighbors at each round of breadth-first search at, stopping as soon as a round adds no new vertex:
a search costs `O((diam G + 1) * (card V) ^ 2)` adjacency tests.

Vertices `u` and `v` are then reachable if `v` lies in the BFS-constructed finset of vertices
reachable from `u`, and a graph is (pre)connected iff it's non-empty and (/empty or) every vertex is
lies in the reachability finset of an arbitrarily-chosen vertex.
-/

section BFS
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} {s t : Finset V} {u v w : V}

variable (G s) in
/-- One round of breadth-first search: `G.bfsStep s` consists of the vertices of `s` together with
their neighbours. -/
def bfsStep : Finset V := {w | w ∈ s ∨ ∃ v ∈ s, G.Adj v w}

/-- Iterate `G.bfsStep` at most `n` times, stopping as soon as no new vertex shows up. -/
def bfsIterate : ℕ → Finset V → Finset V
  | 0, s => s
  | n + 1, s => if (G.bfsStep s).card ≤ s.card then s else bfsIterate n (G.bfsStep s)

/-- The finset of vertices reachable from `u`, computed by breadth-first search. -/
def reachableFinset (u : V) : Finset V := G.bfsIterate (Fintype.card V) {u}
end BFS
end SimpleGraph
