import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_6_5
open Chapter6
open Chapter6.Sequence


/--
[Sequence.lim_of_power_decay](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_5.lean)
-/
@[path]
private lemma main
  {k:ℕ} :
-- imply
  ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 :=
-- proof
  Chapter6.Sequence.lim_of_power_decay


-- created on 2026-10-22
