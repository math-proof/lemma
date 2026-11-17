/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Trails
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/
public section




namespace SimpleGraph

/-- A loopless multigraph whose parallel edges are distinguished by an edge type. -/
structure EdgeIndexedMultigraph (V : Type*) (E : Type*) where
  /-- The unordered endpoints of an edge. -/
  ends : E → Sym2 V
  /-- No edge has two equal endpoints. -/
  loopless : ∀ e v, ends e ≠ s(v, v)

end SimpleGraph
