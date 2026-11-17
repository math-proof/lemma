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
public import Def.Combinatorics.SimpleGraph.FleischnerStrong
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

/-- A rooted cyclic listing witnessing a Hamiltonian cycle in the square, with original-graph
edges at the root. -/
structure StrongSquareCycleListing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) where
  vertices : List V
  first : V
  last : V
  frontRest : List V
  backRest : List V
  front_shape : vertices = x :: first :: frontRest
  back_shape : vertices = backRest ++ [last, x]
  four_le_length : 4 ≤ vertices.length
  square_chain : vertices.IsChain G.square.Adj
  tail_nodup : vertices.tail.Nodup
  mem_tail : ∀ v, v ∈ vertices.tail
  first_adj : G.Adj x first
  last_adj : G.Adj last x

end SimpleGraph

namespace SimpleGraph

namespace Walk

/-- A finite indexed multigraph covering one component outside a cycle. -/
structure ComponentTrailCover (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) where
  /-- Edge identities, including identities for parallel copies. -/
  Edge : Type u
  edge_finite : Finite Edge
  /-- The indexed multigraph carried by the cover. -/
  multigraph : EdgeIndexedMultigraph V Edge
  /-- Every cover edge is an edge of the square. -/
  square_adj : ∀ e, multigraph.ends e ∈ G.square.edgeSet
  /-- Every cover edge has an endpoint in the component. -/
  meets_component : ∀ e, ∃ v ∈ c.componentVertices D, v ∈ multigraph.ends e
  /-- The other endpoints lie either in the component or on the cycle. -/
  endpoints_mem : ∀ e v, v ∈ multigraph.ends e →
    v ∈ c.componentVertices D ∨ v ∈ c.support
  /-- Edges incident with the cycle are original graph edges. -/
  cycle_edge : ∀ e u v, multigraph.ends e = s(u, v) →
    (u ∈ c.support ∨ v ∈ c.support) → G.Adj u v
  /-- Each component vertex has degree two in the cover. -/
  degree_eq_two : ∀ v ∈ c.componentVertices D, multigraph.degree v = 2
  /-- Each component vertex is connected by cover edges to the cycle. -/
  reachable_cycle : ∀ v ∈ c.componentVertices D,
    ∃ w ∈ c.support, multigraph.underlying.Reachable v w

end Walk
end SimpleGraph
