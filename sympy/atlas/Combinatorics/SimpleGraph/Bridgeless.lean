/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Bridgeless.lean -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SimpleGraph

/-- A simple graph is bridgeless when no edge is a bridge. -/
def IsBridgeless {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

variable {V : Type*} {G : SimpleGraph V}

/-- Unfolding of `IsBridgeless`. -/
theorem isBridgeless_iff : G.IsBridgeless ↔ ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
  Iff.rfl

/-- Constructor for `IsBridgeless` from pointwise non-bridge data. -/
theorem IsBridgeless.mk (h : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) : G.IsBridgeless :=
  h

/-- Every edge of a bridgeless graph is not a bridge. -/
theorem IsBridgeless.not_isBridge (h : G.IsBridgeless) {e : Sym2 V}
    (he : e ∈ G.edgeSet) : ¬ G.IsBridge e :=
  h e he

/-- The edgeless graph is vacuously bridgeless. -/
theorem isBridgeless_bot (V : Type*) : (⊥ : SimpleGraph V).IsBridgeless := by
  intro e he
  simp at he

end SimpleGraph
