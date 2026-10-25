/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Lemma.SimpleGraph.EulerCircuit
import Inductive.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
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

/-- The vertices of an indexed walk, including both endpoints. -/
def support {u v : V} : M.IndexedWalk u v → List V
  | .nil w => [w]
  | .cons _ _ p => u :: p.support

/-- The edge identities traversed by an indexed walk. -/
def edges {u v : V} : M.IndexedWalk u v → List E
  | .nil _ => []
  | .cons e _ p => e :: p.edges

/-- An indexed walk is a trail when it uses no edge identity twice. -/
def IsTrail {u v : V} (p : M.IndexedWalk u v) : Prop :=
  p.edges.Nodup

/-- An indexed trail is Eulerian when it uses every edge identity. -/
def IsEulerian {u v : V} (p : M.IndexedWalk u v) : Prop :=
  p.IsTrail ∧ ∀ e, e ∈ p.edges

end IndexedWalk
end EdgeIndexedMultigraph
end SimpleGraph
