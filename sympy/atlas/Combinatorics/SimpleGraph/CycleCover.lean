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

/-- The edges traversed by a cycle. -/
def Cycle.edges {G : SimpleGraph V} (c : Cycle G) : List (Sym2 V) :=
  c.walk.edges

/-- The length of a cycle. -/
def Cycle.length {G : SimpleGraph V} (c : Cycle G) : ℕ :=
  c.walk.length

/-- `C` covers `G`: every edge of `G` lies on at least one cycle of `C`. -/
def IsCycleCover (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) : Prop :=
  ∀ e ∈ G.edgeFinset, ∃ c ∈ C, e ∈ c.edges

/-- The total length of a multiset of cycles. -/
def totalLength {G : SimpleGraph V} (C : Multiset (Cycle G)) : ℕ :=
  (C.map Cycle.length).sum

end SimpleGraph
