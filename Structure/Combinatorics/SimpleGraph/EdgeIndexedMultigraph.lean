/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Lemma.SimpleGraph.EulerCircuit
/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/


namespace SimpleGraph

/-- A loopless multigraph whose parallel edges are distinguished by an edge type. -/
structure EdgeIndexedMultigraph (V : Type*) (E : Type*) where
  /-- The unordered endpoints of an edge. -/
  ends : E → Sym2 V
  /-- No edge has two equal endpoints. -/
  loopless : ∀ e v, ends e ≠ s(v, v)

end SimpleGraph
