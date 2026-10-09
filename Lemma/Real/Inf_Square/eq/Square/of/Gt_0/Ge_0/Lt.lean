import sympy.sets.sets
import sympy.Basic
import Lemma.Real.Inf.eq.Mul.of.Gt_0
import Lemma.Real.Inf_Square.eq.Square.of.Ge_0.Lt


@[path]
private lemma main
  {a m M : ℝ}
-- given
  (ha : a > 0)
  (hm : m ≥ 0)
  (h : m < M) :
-- imply
  sInf ((fun x => x ^ 2 * a) '' Set.Ioo m M) = m ^ 2 * a := by
-- proof
  have h1 : sInf ((fun x => x ^ 2 * a) '' Set.Ioo m M)
      = a * sInf ((fun x => x ^ 2) '' Set.Ioo m M) :=
    Real.Inf.eq.Mul.of.Gt_0 (f := fun x : ℝ => x ^ 2) ha
  rw [h1, Real.Inf_Square.eq.Square.of.Ge_0.Lt hm h]
  exact mul_comm a (m ^ 2)


-- created on 2021-10-02
