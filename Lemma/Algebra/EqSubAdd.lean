import sympy.functions.elementary.integers
import Lemma.Algebra.Add
open Algebra


@[main]
private lemma left.int
  [IntegerRing Z]
  {a b : Z} :
-- imply
  b + a - b = a := by
-- proof
  have := IntegerRing.add_sub_cancel a b
  rw [Add.comm] at this
  assumption


@[main]
private lemma int
  [IntegerRing Z]
  {a b : Z} :
-- imply
  a + b - b = a := by
-- proof
  apply IntegerRing.add_sub_cancel


@[main]
private lemma left
  [AddCommGroup α]
  {a b : α} :
-- imply
  a + b - a = b := by
-- proof
  apply add_sub_cancel_left


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  a + b - b = a := by
-- proof
  apply add_sub_cancel_right


-- created on 2024-11-27
