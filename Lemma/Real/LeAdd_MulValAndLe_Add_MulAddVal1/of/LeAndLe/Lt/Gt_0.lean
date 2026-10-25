import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval


/--
[findSubintervalIndex_spec](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {lo hi : ℝ}
  {n : ℕ}
  {x : ℝ}
-- given
  (hn : n > 0)
  (hlohi : lo < hi)
  (hx : lo ≤ x ∧ x ≤ hi) :
-- imply
  (let k := findSubintervalIndex lo hi n hn x hx
      let Δ := (hi - lo) / n
      lo + k.val * Δ ≤ x ∧ x ≤ lo + (k.val + 1) * Δ) :=
-- proof
  findSubintervalIndex_spec lo hi n hn hlohi x hx


-- created on 2026-10-22
