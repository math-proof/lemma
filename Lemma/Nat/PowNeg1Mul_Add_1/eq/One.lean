import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [Ring α]
-- given
  (n : ℕ) :
-- imply
  (-1 : α) ^ (n * (n + 1)) = 1 :=
-- proof
  Even.neg_one_pow (Nat.even_mul_succ_self n)


-- created on 2020-02-29
