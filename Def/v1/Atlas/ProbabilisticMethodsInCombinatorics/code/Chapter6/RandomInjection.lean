/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/RandomInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.RandomInjection
set_option maxHeartbeats 800000

open Finset


namespace RandomInjection

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- The set of left vertices covered by the bipartite matching $F$. -/
def BipartiteMatching.leftVertices (F : BipartiteMatching X Y) : Finset X :=
  F.edges.image Prod.fst

/-- The set of right vertices covered by the bipartite matching $F$. -/
def BipartiteMatching.rightVertices (F : BipartiteMatching X Y) : Finset Y :=
  F.edges.image Prod.snd

/-- A bipartite matching is complete (a perfect matching from $X$) if every left vertex is covered. -/
def BipartiteMatching.IsComplete [Fintype X] (M : BipartiteMatching X Y) : Prop :=
  M.leftVertices = Finset.univ

/-- Two bipartite matchings are vertex-disjoint if their left vertex sets and their right vertex sets are both disjoint. -/
def VertexDisjoint (F₁ F₂ : BipartiteMatching X Y) : Prop :=
  Disjoint F₁.leftVertices F₂.leftVertices ∧ Disjoint F₁.rightVertices F₂.rightVertices

/-- Canonical dependency graph for a family $(F_i)$ of matchings (Setup 6.5.4): vertices are the indices, and $i, j$ are adjacent when they are distinct and the matchings $F_i, F_j$ share a left or right endpoint. -/
def CanonicalNegDepGraph {n : ℕ} (F : Fin n → BipartiteMatching X Y) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ¬VertexDisjoint (F i) (F j)
  symm := by
    intro i j ⟨hne, hnotdisj⟩
    refine ⟨hne.symm, fun h => hnotdisj ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun i ⟨hne, _⟩ => hne rfl⟩

end RandomInjection
