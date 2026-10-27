import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.SimpleGraph.SimplexGraph
open scoped symmDiff
open SimpleGraph


namespace SimpleGraph

/--
[adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SimplexGraph.lean)
-/
@[path]
lemma adj_iff
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : SimplexVertex G} :
-- imply
  (simplexGraph G).Adj x y ↔ (x.val ∆ y.val).card = 1 :=
-- proof
  Iff.rfl

end SimpleGraph

namespace SimpleGraph

/--
[empty_adj_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SimplexGraph.lean)
-/
@[path]
lemma empty_adj_singleton
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V} :
-- imply
  (simplexGraph G).Adj (emptyVertex G) (singletonVertex G v) := by
-- proof
  change ((∅ : Finset V) ∆ ({v} : Finset V)).card = 1
  rw [Finset.symmDiff_def]
  simp

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-26
