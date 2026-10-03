import Lemma.Real.LtIntegralS.of.All_Lt
import sympy.Basic
open Real


@[main]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x : ℝ, g x < f x) :
-- imply
  ∫ x : ℝ in a..b, f x > ∫ x : ℝ in a..b, g x := by
-- proof
  exact GtIntegralS.of.All_Gt hab hfi hgi fun x _ => h x


-- created on 2026-10-02
