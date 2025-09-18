import Lemma.Algebra.GtAddS.is.Gt
import Lemma.Algebra.EqAdd0
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b : α}
-- given
  (h : a > 0) :
-- imply
  b < a + b := by
-- proof
  have := GtAddS.of.Gt b h
  rw [EqAdd0] at this
  assumption


@[main]
private lemma nat
  {a b : ℕ}
-- given
  (h : a > 0) :
-- imply
  b < a + b := by
-- proof
  have := GtAddS.of.Gt b h
  rw [EqAdd0] at this
  assumption


-- created on 2025-05-24
