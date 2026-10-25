import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_4
open Chapter8


/--
[exist_tendsTo_sup_of_closed](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_4.lean)
-/
@[path]
private lemma main
  {E: Set ℝ}
-- given
  (hnon: E.Nonempty)
  (hbound: BddAbove E)
  (hclosed: IsClosed E) :
-- imply
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) :=
-- proof
  Chapter8.exist_tendsTo_sup_of_closed hnon hbound hclosed


-- created on 2026-10-22
