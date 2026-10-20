/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SimplexGraph.lean -/

import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped symmDiff

/-!
# Finite simplex graphs

Finite simplex graph construction following Huang, Xie, Xu arXiv:2608.25416v1 lines 193-197.
Vertices are the cliques of the base graph; two vertices are adjacent when their
symmetric difference has cardinality one.
The construction conservatively generalizes the cited finite-graph definition
by omitting Fintype; finiteness is not needed for the adjacency API.
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

@[expose]

/-- `SimplexVertex G` is the clique subtype: finsets of vertices that are cliques of `G`. -/
def SimplexVertex := { s : Finset V // G.IsClique (↑s : Set V) }

/-- The empty clique as a simplex vertex. -/
def emptyVertex : SimplexVertex G := ⟨∅, by simp⟩

/-- The singleton clique as a simplex vertex. -/
def singletonVertex (v : V) : SimplexVertex G := ⟨{v}, by simp⟩

/-- The finite simplex graph: adjacency by symmetric-difference cardinality one. -/
def simplexGraph : SimpleGraph (SimplexVertex G) where
  Adj x y := (x.val ∆ y.val).card = 1
  symm := ⟨by
    intro x y h
    simpa only [symmDiff_comm] using h⟩
  loopless := ⟨by
    intro x h
    rw [Finset.symmDiff_def] at h
    simp at h⟩

/-- Adjacency unfolds to symmetric-difference cardinality one. -/
theorem adj_iff (x y : SimplexVertex G) :
    (simplexGraph G).Adj x y ↔ (x.val ∆ y.val).card = 1 := Iff.rfl

/-- The empty clique is adjacent to every singleton clique. -/
theorem empty_adj_singleton (v : V) :
    (simplexGraph G).Adj (emptyVertex G) (singletonVertex G v) := by
  change ((∅ : Finset V) ∆ ({v} : Finset V)).card = 1
  rw [Finset.symmDiff_def]
  simp

end SimpleGraph
