import Lemma.Real.Sup.eq.Add_Mul.of.Lt_0.Lt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m M a b : ℝ}
-- given
  (ha : a < 0)
  (h : m < M) :
-- imply
  sSup ((fun x : ℝ => a * x + b) '' Set.Ioo m M) =
    max (a * m + b) (a * M + b) := by
-- proof
  rw [Real.Sup.eq.Add_Mul.of.Lt_0.Lt ha h, max_eq_left]
  linarith [mul_lt_mul_of_neg_left h ha]


-- created on 2019-12-23
