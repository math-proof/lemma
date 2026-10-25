/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected


namespace SimpleGraph

/-- A simple graph is bridgeless when no edge is a bridge. -/
def IsBridgeless {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

end SimpleGraph
