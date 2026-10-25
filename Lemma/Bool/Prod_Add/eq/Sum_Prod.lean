import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.Combinatorics


/--
[prod_add_eq_sum_prod_choice](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Combinatorics.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {a b : Fin d → ℝ} :
-- imply
  ∏ i, (a i + b i) = ∑ c : Fin d → Bool, ∏ i, (if c i then b i else a i) :=
-- proof
  Fin.prod_add_eq_sum_prod_choice d a b


-- created on 2026-10-20
