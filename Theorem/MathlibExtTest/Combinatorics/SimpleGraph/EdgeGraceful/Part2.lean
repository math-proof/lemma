module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Def.Combinatorics.SimpleGraph.EdgeGraceful
public import Theorem.SimpleGraph.EdgeGraceful
public import Def.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/
namespace EdgeGracefulTest

theorem he01 : ((e01 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) =
    Sym2.mk (0 : Fin 3) 1 := rfl

theorem he12 : ((e12 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) =
    Sym2.mk (1 : Fin 3) 2 := rfl

end EdgeGracefulTest
