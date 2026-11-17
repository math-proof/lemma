/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Def.Combinatorics.SimpleGraph.StrongSquareCycle
public import Lemma.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.VertexConnectivity
public import Lemma.SimpleGraph.Contraction
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Lemma.SimpleGraph.Riha
public import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
public import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Def.Combinatorics.SimpleGraph.Riha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.ZMod.Basic
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part21
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/
public section



/-! ## CycleComplement -/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

namespace CyclicCircuit

universe u v

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)

variable (C : M.CyclicCircuit)

/-- Data ensuring that deleting the marked passes of a cyclic Euler circuit gives a rooted
Hamiltonian cycle in the square. -/
structure SquareMarking [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) where
  start : Fin C.size
  root_start : C.vertex start = root
  marked : Fin C.size → Bool
  start_unmarked : marked start = false
  unique_unmarked : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false
  two_le_size : 2 ≤ C.size
  three_le_card : 3 ≤ Fintype.card V
  marked_square_chain :
    (C.markedVertexListing M start marked).IsChain (MarkedSquareStep G)
  no_backtrack : MarkedNoBacktrack (C.markedVertexListing M start marked)
  next_unmarked : marked (cyclicNext C.size C.size_pos start) = false
  prev_unmarked : marked (cyclicPrev C.size C.size_pos start) = false
  next_adj : G.Adj root (C.vertex (cyclicNext C.size C.size_pos start))
  prev_adj : G.Adj (C.vertex (cyclicPrev C.size C.size_pos start)) root

end CyclicCircuit
end EdgeIndexedMultigraph
end SimpleGraph
