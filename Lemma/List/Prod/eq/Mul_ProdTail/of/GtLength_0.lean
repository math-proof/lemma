import Lemma.List.Eq_Cons_Tail.of.GtLength_0
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Algebra.ProdCons.eq.Mul_Prod
open Algebra Logic List


@[main]
private lemma main
  [Mul α] [One α]
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v.prod = v[0] * v.tail.prod := by
-- proof
  have := Eq_Cons_Tail.of.GtLength_0 h
  have := EqUFnS.of.Eq this (·.prod)
  rw [this]
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-06-09
