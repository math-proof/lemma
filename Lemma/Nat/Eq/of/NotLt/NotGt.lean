import Lemma.Nat.Eq.of.Le.Ge
import Lemma.Nat.NotGt.is.Le
import Lemma.Nat.Ge.of.NotLt
open Nat


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
