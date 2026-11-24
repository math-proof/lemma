module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Theorem.SimpleGraph.EulerCircuit
public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/
namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

instance [DecidableEq V] : DecidableRel M.incidenceGraph.Adj := by
  intro a b
  cases a <;> cases b <;> simp only [incidenceGraph, Inc] <;> infer_instance

end EdgeIndexedMultigraph
end SimpleGraph
