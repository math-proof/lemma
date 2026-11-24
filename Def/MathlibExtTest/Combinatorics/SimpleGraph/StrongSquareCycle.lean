module
public import Def.Combinatorics.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.StrongSquareCycle
public import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/StrongSquareCycle.lean -/
namespace MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle

def triangleWalk :
    (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0 :=
  .cons adj_zero_one (.cons adj_one_two (.cons adj_two_zero .nil))

end MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle
