import Lemma.Real.Sup.eq.Mul.Inf.of.Lt_0
import Lemma.Real.Inf_Square.eq.Square.of.Ge_0.Lt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a m M : ℝ}
-- given
  (ha : a < 0)
  (hm : m ≥ 0)
  (h : m < M) :
-- imply
  sSup ((fun x => x ^ 2 * a) '' Set.Ioo m M) = m ^ 2 * a := by
-- proof
  rw [Real.Sup.eq.Mul.Inf.of.Lt_0 ha (f := fun x => x ^ 2),
    Real.Inf_Square.eq.Square.of.Ge_0.Lt hm h]
  ring


-- created on 2021-10-02
