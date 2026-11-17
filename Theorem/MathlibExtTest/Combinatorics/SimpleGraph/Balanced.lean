/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Balanced.lean -/
module

public import Def.Combinatorics.SimpleGraph.Balanced

public section

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (h : (G.maxDegree : ℝ) ≤ 1 * (G.minDegree : ℝ)) :
    SimpleGraph.IsBalanced G 1 := h

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    SimpleGraph.IsBalanced G 1 ↔
      (G.maxDegree : ℝ) ≤ 1 * (G.minDegree : ℝ) :=
  Iff.rfl

