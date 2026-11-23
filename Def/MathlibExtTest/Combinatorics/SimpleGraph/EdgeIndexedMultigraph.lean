/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean -/

module

public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Mathlib.Tactic.FinCases

@[expose] public section

open scoped BigOperators


namespace MathlibExtTest.EdgeIndexedMultigraph

open SimpleGraph

def single : EdgeIndexedMultigraph (Fin 2) Unit where
  ends _ := s(0, 1)
  loopless := by
    intro _ v
    fin_cases v <;> decide

def double : EdgeIndexedMultigraph (Fin 2) (Unit ⊕ Unit) :=
  single.disjointSum single

end MathlibExtTest.EdgeIndexedMultigraph
