import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {n : ℕ} :
-- imply
  (ascPochhammer ℝ n).eval x = (-1) ^ n * (descPochhammer ℝ n).eval (-x) := by
-- proof
  have e := ascPochhammer_eval_neg_eq_descPochhammer ℝ (-x) n
  rwa [neg_neg] at e


-- created on 2023-08-20
