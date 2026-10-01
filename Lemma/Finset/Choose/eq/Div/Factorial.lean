import Mathlib.Data.Nat.Choose.Multinomial
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i j k : ℕ}
-- given
  (h : n = i + j + k) :
-- imply
  (Nat.multinomial Finset.univ ![i, j, k] : ℝ) = (n.factorial : ℝ) / (i.factorial * j.factorial * k.factorial) := by
-- proof
  have hs := Nat.multinomial_spec Finset.univ ![i, j, k]
  rw [Fin.prod_univ_three, Fin.sum_univ_three] at hs
  rw [eq_div_iff (by positivity), h]
  have e : (i.factorial * j.factorial * k.factorial) * Nat.multinomial Finset.univ ![i, j, k] = (i + j + k).factorial := hs
  rw [← e]
  push_cast
  ring


-- created on 2023-08-20
