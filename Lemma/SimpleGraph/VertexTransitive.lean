import Mathlib
import sympy.Basic
import Theorem.Combinatorics.SimpleGraph.VertexTransitive
open SimpleGraph


/--
[isVertexTransitive_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexTransitive.lean)
-/
@[path]
private lemma isVertexTransitive_of_subsingleton_eq
  [Subsingleton V]
  {G : SimpleGraph V} :
-- imply
  G.IsVertexTransitive := by
-- proof
  apply SimpleGraph.isVertexTransitive_of_subsingleton G


-- created on 2026-10-20
