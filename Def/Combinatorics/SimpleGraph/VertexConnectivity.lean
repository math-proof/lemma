/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
/-!
# Vertex connectivity

A shared vertex-connectivity predicate for finite simple graphs.
-/


namespace SimpleGraph

/-- `IsVertexConnected k G` means that `G` has more than `k` vertices and
stays connected after removing any set of fewer than `k` vertices. -/
def IsVertexConnected {V : Type*} [Fintype V] (k : ℕ) (G : SimpleGraph V) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected

end SimpleGraph
