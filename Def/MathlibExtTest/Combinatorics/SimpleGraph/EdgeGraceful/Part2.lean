module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Def.Combinatorics.SimpleGraph.EdgeGraceful
public import Theorem.SimpleGraph.EdgeGraceful
public import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/
namespace EdgeGracefulTest

def pathToFun : (SimpleGraph.pathGraph 3).edgeSet → Fin 2 :=
  fun e => if e.val = Sym2.mk (0 : Fin 3) 1 then 0 else 1

def pathInvFun : Fin 2 → (SimpleGraph.pathGraph 3).edgeSet :=
  fun k => if k = 0 then e01 else e12

end EdgeGracefulTest
