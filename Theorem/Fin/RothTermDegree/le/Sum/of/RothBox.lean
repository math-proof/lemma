module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.RothAuxiliary.Part3
public import Def.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


public section

/--
[rothTermDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
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
