/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/
module

public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Mathlib.Tactic.FinCases
public import Def.MathlibExtTest.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
open scoped BigOperators

public section

namespace MathlibExtTest.EdgeIndexedMultigraph

open SimpleGraph

example : double.ends (Sum.inl ()) = double.ends (Sum.inr ()) := by
  rw [double, SimpleGraph.EdgeIndexedMultigraph.disjointSum_ends_inl,
    SimpleGraph.EdgeIndexedMultigraph.disjointSum_ends_inr]

theorem first_ends : double.ends (Sum.inl ()) = s(0, 1) :=
  rfl

theorem second_ends : double.ends (Sum.inr ()) = s(1, 0) := by
  rw [Sym2.eq_swap]
  rfl

end MathlibExtTest.EdgeIndexedMultigraph
