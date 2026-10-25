/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Lemma.SimpleGraph.EulerCircuit
import Instance.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- Keep the edge-index vertices from a list in the incidence subdivision. -/
def edgeProjection : List (V ⊕ E) → List E
  | [] => []
  | Sum.inl _ :: l => edgeProjection l
  | Sum.inr e :: l => e :: edgeProjection l

end EdgeIndexedMultigraph
end SimpleGraph
