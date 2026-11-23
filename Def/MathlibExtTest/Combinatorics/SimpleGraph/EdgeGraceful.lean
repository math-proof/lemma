/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Def.Combinatorics.SimpleGraph.EdgeGraceful
public import Theorem.SimpleGraph.EdgeGraceful
public import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful

@[expose] public section

namespace EdgeGracefulTest

/-- First edge of the 3-vertex path. -/
def e01 : (SimpleGraph.pathGraph 3).edgeSet :=
  ⟨Sym2.mk (0 : Fin 3) 1,
    (SimpleGraph.mem_edgeSet _).mpr (by simp [SimpleGraph.pathGraph_adj])⟩

/-- Second edge of the 3-vertex path. -/
def e12 : (SimpleGraph.pathGraph 3).edgeSet :=
  ⟨Sym2.mk (1 : Fin 3) 2,
    (SimpleGraph.mem_edgeSet _).mpr (by simp [SimpleGraph.pathGraph_adj])⟩

end EdgeGracefulTest
