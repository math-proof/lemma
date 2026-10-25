/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/LongestCycle.lean -/

import Mathlib.Combinatorics.SimpleGraph.Paths
/-!
# Longest cycles in simple graphs

This file provides the predicate that a closed walk is a cycle of maximum
length among all cycles in the same graph.
-/


namespace SimpleGraph.Walk

/-- A cycle is globally longest if no cycle in the graph has more edges. -/
def IsLongestCycle {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) : Prop :=
  p.IsCycle ∧ ∀ (w : V) (q : G.Walk w w), q.IsCycle → q.length ≤ p.length

end SimpleGraph.Walk
