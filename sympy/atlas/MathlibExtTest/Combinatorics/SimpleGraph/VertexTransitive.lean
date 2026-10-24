/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/VertexTransitive.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.VertexTransitive
import Lemma.SimpleGraph.VertexTransitive


open SimpleGraph

example (G : SimpleGraph (Fin 1)) : G.IsVertexTransitive := by simp
