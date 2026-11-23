/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/VertexTransitive.lean -/
module

public import Theorem.Combinatorics.SimpleGraph.VertexTransitive
public import Theorem.SimpleGraph.VertexTransitive
open SimpleGraph

public section

example (G : SimpleGraph (Fin 1)) : G.IsVertexTransitive := by simp

