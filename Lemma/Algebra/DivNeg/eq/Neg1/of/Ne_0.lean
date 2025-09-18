import Lemma.Algebra.Div.eq.One.of.Ne_0
import Lemma.Algebra.DivNeg.eq.NegDiv
import Lemma.Algebra.EqNegS.is.Eq
open Algebra


@[main]
private lemma main
  [Field α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  -a / a = -1 := by
-- proof
  rw [DivNeg.eq.NegDiv]
  have := Div.eq.One.of.Ne_0 h
  apply EqNegS.of.Eq this


-- created on 2025-03-20
