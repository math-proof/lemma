import Lemma.Real.Sup.eq.Add_Mul.of.Gt_0.Lt
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {m M a b : ℝ}
-- given
  (ha : 0 < a)
  (h : m < M) :
-- imply
  sSup ((fun x : ℝ => a * x + b) '' Set.Ioo m M) =
    max (a * m + b) (a * M + b) := by
-- proof
  rw [Real.Sup.eq.Add_Mul.of.Gt_0.Lt ha h, max_eq_right]
  linarith [mul_lt_mul_of_pos_left h ha]


-- created on 2019-09-11
