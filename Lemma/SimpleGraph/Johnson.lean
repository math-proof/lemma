import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.SimpleGraph.Johnson
open SimpleGraph


namespace SimpleGraph

/--
[johnsonGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Johnson.lean)
-/
@[path]
lemma johnsonGraph_adj_iff
  {n k : ℕ}
  {s t : {s : Finset (Fin n) // s.card = k}} :
-- imply
  (johnsonGraph n k).Adj s t ↔ (s.val ∩ t.val).card + 1 = k :=
-- proof
  Iff.rfl

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-26
