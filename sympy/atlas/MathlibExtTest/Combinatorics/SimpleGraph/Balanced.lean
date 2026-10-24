/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Balanced.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.Balanced

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (h : (G.maxDegree : ℝ) ≤ 1 * (G.minDegree : ℝ)) :
    SimpleGraph.IsBalanced G 1 := h

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    SimpleGraph.IsBalanced G 1 ↔
      (G.maxDegree : ℝ) ≤ 1 * (G.minDegree : ℝ) :=
  Iff.rfl
