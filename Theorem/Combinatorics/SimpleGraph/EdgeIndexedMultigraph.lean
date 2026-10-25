/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Lemma.SimpleGraph.EulerCircuit
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

namespace IndexedWalk

/-- Prepending an indexed edge prepends its identity to the edge list. -/
@[simp]
theorem edges_cons {u v w : V} (e : E) (he : M.ends e = s(u, v))
    (p : M.IndexedWalk v w) : (IndexedWalk.cons e he p).edges = e :: p.edges :=
  rfl

end IndexedWalk
end EdgeIndexedMultigraph
end SimpleGraph
