/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/


import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
open scoped BigOperators


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
