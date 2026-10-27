import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_4
open Chapter8


/--
[exist_tendsTo_sup](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_4.lean)
-/
@[path]
private lemma main
  {E: Set ℝ}
-- given
  (hnon: E.Nonempty)
  (hbound: BddAbove E) :
-- imply
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) :=
-- proof
  Chapter8.exist_tendsTo_sup hnon hbound


-- created on 2026-10-22
