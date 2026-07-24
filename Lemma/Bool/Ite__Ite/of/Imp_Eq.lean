import sympy.core.relational
import Lemma.Bool.EqIteS.of.Imp_Eq
open Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {f : α → α}
  {x a b c : α}
-- given
  (h : p → x = a) :
-- imply
  (if q then
    b
  else if p then
    f x
  else
    c) = if q then
    b
  else if p then
    f a
  else
    c := by
-- proof
  denote h_Ite : A = if p then
    f x
  else
    c
  have := EqIteS.of.Imp_Eq (f := f) (b := c) h
  rw [this]


-- created on 2025-04-19
