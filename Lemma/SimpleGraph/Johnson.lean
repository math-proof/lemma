import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Johnson
open SimpleGraph


/--
[johnsonGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Johnson.lean)
-/
@[path]
private lemma johnsonGraph_adj_iff_eq
  {n k : ℕ}
  {s t : {s : Finset (Fin n) // s.card = k}} :
-- imply
  (johnsonGraph n k).Adj s t ↔ (s.val ∩ t.val).card + 1 = k := by
-- proof
  apply SimpleGraph.johnsonGraph_adj_iff n k s t


-- created on 2026-10-20
