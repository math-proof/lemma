import Mathlib.Data.Nat.Choose.Basic
import sympy.functions.combinatorial.factorials
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  n.choose k = n.descFactorial k / k ! :=
-- proof
  Nat.choose_eq_descFactorial_div_factorial n k


@[main]
private lemma doit
  {n : ℕ} :
-- imply
  n.choose 3 = n * (n - 1) * (n - 2) / 3 ! := by
-- proof
  rw [Nat.choose_eq_descFactorial_div_factorial]
  congr 1
  simp [Nat.descFactorial]
  ring


-- created on 2020-02-28
-- updated on 2026-09-27
