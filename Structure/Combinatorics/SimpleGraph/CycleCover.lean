/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CycleCover.lean -/

import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Multiset.Basic


namespace SimpleGraph

variable {V : Type*}

/-- A cycle in a graph, presented as a closed walk with a cycle proof. -/
structure Cycle (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle

end SimpleGraph
