module
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Theorem.Combinatorics.SimpleGraph.Square
public import Theorem.SimpleGraph.Square
public import Instance.MathlibExtTest.Combinatorics.SimpleGraph.Square


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean -/
namespace MathlibExtTest.Combinatorics.SimpleGraph.Square

example : 4 ≤ (⊤ : SimpleGraph (Fin 5)).square.degree 0 :=
  completeGraph_isVertexConnected_two.four_le_square_degree (by decide) 0

end MathlibExtTest.Combinatorics.SimpleGraph.Square
