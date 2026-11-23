/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

module

public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Mathlib.Tactic.FinCases
public import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EdgeIndexedMultigraph

@[expose] public section

open scoped BigOperators


namespace MathlibExtTest.EdgeIndexedMultigraph

open SimpleGraph

def circuitTail : double.IndexedWalk 1 0 :=
  .cons (Sum.inr ()) second_ends (.nil 0)

def circuit : double.IndexedWalk 0 0 :=
  .cons (Sum.inl ()) first_ends circuitTail

end MathlibExtTest.EdgeIndexedMultigraph
