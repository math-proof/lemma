import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Misc.FiniteChoice


/--
[sec_ex](https://github.com/teorth/analysis/blob/main/Analysis/Misc/FiniteChoice.lean)
-/
@[path]
private lemma main
  {α β:Type*} [Fintype β] [DecidableEq β]
  {f : α → β}
-- given
  (h : ∀ b: β, ∃ a : α, f a = b) :
-- imply
  ∃ s :β → α, f ∘ s = id :=
-- proof
  sec_ex f h


-- created on 2026-10-22
