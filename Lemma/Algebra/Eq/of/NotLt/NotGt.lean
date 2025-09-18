import Lemma.Algebra.Eq.of.Le.Ge
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.Ge.of.NotLt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h₀ : ¬a < b)
  (h₁ : ¬a > b) :
-- imply
  a = b := by
-- proof
  apply Eq.of.Le.Ge
  apply Le.of.NotGt h₁
  apply Ge.of.NotLt h₀


-- created on 2025-03-23
