import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {n : ℕ} :
-- imply
  (descPochhammer ℝ n).eval x = n.factorial * Ring.choose x n := by
-- proof
  have e := Ring.descPochhammer_eq_factorial_smul_choose x n
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, descPochhammer_map,
    nsmul_eq_mul] at e
  exact e


-- created on 2023-08-27
