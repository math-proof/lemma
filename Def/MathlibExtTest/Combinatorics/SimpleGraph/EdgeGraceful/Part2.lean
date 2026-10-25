/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Def.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful.Part2


namespace EdgeGracefulTest

def pathToFun : (SimpleGraph.pathGraph 3).edgeSet → Fin 2 :=
  fun e => if e.val = Sym2.mk (0 : Fin 3) 1 then 0 else 1

def pathInvFun : Fin 2 → (SimpleGraph.pathGraph 3).edgeSet :=
  fun k => if k = 0 then e01 else e12

end EdgeGracefulTest
