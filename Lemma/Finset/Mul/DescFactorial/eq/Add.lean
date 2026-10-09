import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℂ}
  {k : ℕ} :
-- imply
  x * (descPochhammer ℂ k).eval x = (descPochhammer ℂ (k + 1)).eval x + k * (descPochhammer ℂ k).eval x := by
-- proof
  rw [descPochhammer_succ_eval]
  ring


-- created on 2023-08-26
