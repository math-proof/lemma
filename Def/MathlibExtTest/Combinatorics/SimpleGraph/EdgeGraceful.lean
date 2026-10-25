/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Def.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful


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
