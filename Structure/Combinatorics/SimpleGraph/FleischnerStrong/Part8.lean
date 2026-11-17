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
public import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part31
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

/-- A finite directed traversal of every edge identity around one circuit. -/
structure CyclicCircuit where
  /-- Number of edge positions. -/
  size : ℕ
  size_pos : 0 < size
  /-- Vertex before the edge at a cyclic position. -/
  vertex : Fin size → V
  /-- Edge traversed from this position to the next one. -/
  edge : Fin size → E
  /-- The indexed edge has the displayed consecutive endpoints. -/
  ends_edge : ∀ i, M.ends (edge i) =
    s(vertex i, vertex (cyclicNext size size_pos i))
  /-- Every edge identity occurs exactly once. -/
  edge_bijective : Function.Bijective edge

end EdgeIndexedMultigraph
end SimpleGraph
