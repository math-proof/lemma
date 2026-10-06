import sympy.integrals.integrals
import sympy.sets.sets
import sympy.Basic
import Lemma.Real.LtIntegral.of.All_Lt


@[main]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x, f x < g x) :
-- imply
  ∫ x : ℝ in a..b, f x < ∫ x : ℝ in a..b, g x :=
-- proof
  Real.LtIntegral.of.All_Lt hab hfi hgi fun x _ => h x


-- created on 2019-12-31
