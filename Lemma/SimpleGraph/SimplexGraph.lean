import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.SimplexGraph
open scoped symmDiff
open SimpleGraph


/--
[adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SimplexGraph.lean)
-/
@[path]
private lemma adj_iff_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : SimplexVertex G} :
-- imply
  (simplexGraph G).Adj x y ↔ (x.val ∆ y.val).card = 1 := by
-- proof
  apply SimpleGraph.adj_iff G x y

/--
[empty_adj_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SimplexGraph.lean)
-/
@[path]
private lemma empty_adj_singleton_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V} :
-- imply
  (simplexGraph G).Adj (emptyVertex G) (singletonVertex G v) := by
-- proof
  apply SimpleGraph.empty_adj_singleton G v


-- created on 2026-10-20
