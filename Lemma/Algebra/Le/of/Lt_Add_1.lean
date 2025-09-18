import Lemma.Algebra.LeAdd_1.of.Lt
import Lemma.Algebra.NotLe.is.Gt
import Lemma.Algebra.GtAddS.is.Gt
import Lemma.Algebra.Gt.of.Gt.Ge
import Lemma.Algebra.NotGt
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x < y + 1) :
-- imply
  x ≤ y := by
-- proof
  have h_Le := LeAdd_1.of.Lt h
  by_contra h'
  have := Gt.of.NotLe h'
  have : x + 1 > y + 1 := GtAddS.of.Gt this (a := 1)
  have := Gt.of.Gt.Ge this h_Le
  have := NotGt (a := x + 1)
  contradiction


-- created on 2025-03-29
