import Lemma.Set.Le.of.In_Ioc
import Lemma.Set.Lt.of.In_Ioc
import Lemma.Real.GtPi0
import sympy.functions.elementary.trigonometric
import sympy.sets.sets
open Set Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ioc (π / 2) π) :
-- imply
  cos x < 0 := by
-- proof
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  ·
    exact Lt.of.In_Ioc h
  ·
    linarith [Le.of.In_Ioc h, GtPi0]


-- created on 2018-06-22
