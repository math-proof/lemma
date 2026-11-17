module

public import Mathlib
public import Theorem.Combinatorics.SimpleGraph.VertexTransitive

public section

open SimpleGraph


/--
[isVertexTransitive_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexTransitive.lean)
-/
public theorem isVertexTransitive_of_subsingleton_eq
  [Subsingleton V]
  {G : SimpleGraph V} :
-- imply
  G.IsVertexTransitive := by
-- proof
  apply SimpleGraph.isVertexTransitive_of_subsingleton G


-- created on 2026-10-20
