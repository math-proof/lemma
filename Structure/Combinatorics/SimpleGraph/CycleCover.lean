/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CycleCover.lean -/

module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Multiset.Basic


public section

namespace SimpleGraph

variable {V : Type*}

/-- A cycle in a graph, presented as a closed walk with a cycle proof. -/
structure Cycle (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle

end SimpleGraph
