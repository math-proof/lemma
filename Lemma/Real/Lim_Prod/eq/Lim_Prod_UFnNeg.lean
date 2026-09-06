import Lemma.Finset.Prod.eq.Prod_UFnNeg
import Lemma.Real.EqLim.of.Eq
import sympy.series.limits
open Finset


@[main]
private lemma main
-- given
  (f : ℤ → ℝ) :
-- imply
  (lim [n → ∞] ∏ i ∈ Finset.Ico (-n) (n + 1), f i) = (lim [n → ∞] ∏ i ∈ Finset.Ico (-n) (n + 1), f (-i)) := by
-- proof
  apply Real.EqLim.of.Eq.inf
  apply funext
  intro n
  apply Prod.eq.Prod_UFnNeg


-- created on 2020-02-25
