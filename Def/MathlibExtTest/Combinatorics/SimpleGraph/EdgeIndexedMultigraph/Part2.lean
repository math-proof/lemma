/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/


import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Mathlib.Tactic.FinCases
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
open scoped BigOperators


namespace MathlibExtTest.EdgeIndexedMultigraph

open SimpleGraph

def circuitTail : double.IndexedWalk 1 0 :=
  .cons (Sum.inr ()) second_ends (.nil 0)

def circuit : double.IndexedWalk 0 0 :=
  .cons (Sum.inl ()) first_ends circuitTail

end MathlibExtTest.EdgeIndexedMultigraph
