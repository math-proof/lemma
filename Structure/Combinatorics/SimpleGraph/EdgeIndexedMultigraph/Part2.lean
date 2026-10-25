/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Lemma.SimpleGraph.EulerCircuit
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part3
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- An incidence trail collapsed to an indexed walk, with its edge-list identity. -/
structure IncidenceCollapse [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) where
  walk : M.IndexedWalk u v
  edges_eq : walk.edges = edgeProjection p.support

end EdgeIndexedMultigraph
end SimpleGraph
