/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Finset

namespace DirectedCycles

variable {V : Type*}

/-- A directed walk in a digraph $G$ from vertex $u$ to vertex $v$: either the empty walk at
$u$, or a step along a directed edge followed by another walk. -/
inductive DirectedWalk (G : Digraph V) : V → V → Type _
  | nil {u : V} : DirectedWalk G u u
  | cons {u v w : V} (h : G.Adj u v) (p : DirectedWalk G v w) : DirectedWalk G u w

namespace DirectedWalk

variable {G : Digraph V}

/-- The length (number of edges) of a directed walk. -/
def length : {u v : V} → DirectedWalk G u v → ℕ
  | _, _, nil => 0
  | _, _, cons _ p => p.length + 1

/-- The list of vertices visited by a directed walk, in order. -/
def support : {u v : V} → DirectedWalk G u v → List V
  | u, _, nil => [u]
  | u, _, cons _ p => u :: p.support

/-- Concatenation of two directed walks meeting at a common vertex. -/
def append : {u v w : V} → DirectedWalk G u v → DirectedWalk G v w → DirectedWalk G u w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => cons h (p.append q)

/-- Recast a directed walk along propositional equalities of its endpoints. -/
def cast {u v u' v' : V} (hu : u = u') (hv : v = v') :
    DirectedWalk G u v → DirectedWalk G u' v' :=
  fun p => hu ▸ hv ▸ p

/-- A directed walk from a vertex to itself is a *cycle* if it has positive length and visits
each vertex at most once (no repeated vertices apart from the start/end). -/
structure IsCycle {u : V} (p : DirectedWalk G u u) : Prop where
  pos_length : p.length > 0
  support_nodup : p.support.tail.Nodup

end DirectedWalk

/-- The digraph $G$ contains a directed cycle whose length is divisible by $k$. -/
def HasDirectedCycleDivisibleBy (G : Digraph V) (k : ℕ) : Prop :=
  ∃ (u : V) (p : DirectedWalk G u u), p.IsCycle ∧ k ∣ p.length

section Degree
variable (G : Digraph V) [Fintype V] [DecidableRel G.Adj] [DecidableEq V]

/-- Out-degree of a vertex $v$ in a digraph: the number of vertices $w$ with $v \to w$. -/
def outDegree (v : V) : ℕ := (Finset.univ.filter (G.Adj v)).card

/-- In-degree of a vertex $v$ in a digraph: the number of vertices $w$ with $w \to v$. -/
def inDegree (v : V) : ℕ := (Finset.univ.filter (fun w => G.Adj w v)).card

/-- A digraph is $d$-regular if every vertex has in-degree and out-degree both equal to $d$. -/
def IsRegular (d : ℕ) : Prop :=
  (∀ v : V, outDegree G v = d) ∧ (∀ v : V, inDegree G v = d)

end Degree

/-- A successor labeling $f : V \to \mathbb{Z}/k\mathbb{Z}$ assigns each vertex $v$ an out-neighbor
$w$ whose label is $f(v) + 1$; following such successors produces a cycle of length divisible
by $k$. -/
def IsSuccessorLabeling (G : Digraph V) (k : ℕ) [NeZero k] (f : V → ZMod k) : Prop :=
  ∀ v : V, ∃ w : V, G.Adj v w ∧ f w = f v + 1

/-- Build the directed walk along the first $m$ steps of a vertex sequence whose consecutive
elements are adjacent. -/
noncomputable def consWalk (G : Digraph V) (seq : ℕ → V)
    (hadj : ∀ n : ℕ, G.Adj (seq n) (seq (n + 1))) :
    (m : ℕ) → DirectedWalk G (seq 0) (seq m)
  | 0 => DirectedWalk.nil
  | m + 1 => DirectedWalk.cons (hadj 0)
    (consWalk G (fun n => seq (n + 1)) (fun n => hadj (n + 1)) m)

/-- Theorem 6.4.1 (Alon-Linial 1989): for every $k \ge 1$ there exists $d$ such that every
$d$-regular digraph contains a directed cycle of length divisible by $k$. -/
def HasCycleDivisibleBy (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ k ∣ p.length

/-- Bridge from the directed to the undirected setting: any $2d$-regular simple graph admits an
Eulerian orientation that is $d$-regular as a digraph, so existence of a directed cycle of
length divisible by $k$ in the orientation yields an undirected cycle of the same length. -/
end DirectedCycles
