import Lemma.Algebra.Ne.of.Gt
import Lemma.Bool.Eq.is.False.of.Ne
open Algebra Bool


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a = b ↔ False := by
-- proof
  have := Ne.of.Gt h
  apply Eq.is.False.of.Ne this


-- created on 2025-03-29
