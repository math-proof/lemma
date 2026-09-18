import Mathlib.Order.Filter.Basic
import sympy.Basic
open Filter


@[main]
private lemma main
  {f : α → β}
  {a : Filter α}
  {b b' : Filter β}
-- given
  (hb : b = b')
  (hf : Tendsto f a b) :
-- imply
  Tendsto f a b' := by
-- proof
  aesop


-- created on 2026-09-18
