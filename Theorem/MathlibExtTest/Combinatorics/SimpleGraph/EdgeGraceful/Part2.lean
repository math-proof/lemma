/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Def.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful
import Def.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful


namespace EdgeGracefulTest

theorem he01 : ((e01 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) =
    Sym2.mk (0 : Fin 3) 1 := rfl

theorem he12 : ((e12 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) =
    Sym2.mk (1 : Fin 3) 2 := rfl

end EdgeGracefulTest
