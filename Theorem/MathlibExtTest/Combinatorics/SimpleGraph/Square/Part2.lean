/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean -/


import Mathlib.Combinatorics.SimpleGraph.Hasse
import Theorem.Combinatorics.SimpleGraph.Square
import Lemma.SimpleGraph.Square
import Instance.MathlibExtTest.Combinatorics.SimpleGraph.Square


namespace MathlibExtTest.Combinatorics.SimpleGraph.Square

example : 4 ≤ (⊤ : SimpleGraph (Fin 5)).square.degree 0 :=
  completeGraph_isVertexConnected_two.four_le_square_degree (by decide) 0

end MathlibExtTest.Combinatorics.SimpleGraph.Square
