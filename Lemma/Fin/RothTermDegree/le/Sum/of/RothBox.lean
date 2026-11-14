import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
import Def.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothTermDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (i j : RothBox r) :
-- imply
  rothTermDegree i j ≤ ∑ h, r h := by
-- proof
  unfold rothTermDegree
  gcongr with h
  exact (Nat.sub_le _ _).trans (Nat.le_of_lt_succ (j h).isLt)


-- updated on 2026-11-13
-- created on 2026-10-21
