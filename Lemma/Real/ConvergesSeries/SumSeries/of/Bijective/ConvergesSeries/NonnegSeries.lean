import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_4
open Chapter7
open Chapter7.Series


/--
[Series.converges_of_permute_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_4.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℝ}
  {f: ℕ → ℕ}
-- given
  (ha: (a:Series).nonneg)
  (hconv: (a:Series).converges)
  (hf: Function.Bijective f) :
-- imply
  (fun n ↦ a (f n) : Series).converges ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum :=
-- proof
  Chapter7.Series.converges_of_permute_nonneg ha hconv hf


-- created on 2026-10-22
