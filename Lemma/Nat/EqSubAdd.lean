import sympy.functions.elementary.integers
import Lemma.Nat.Add
open Nat


@[path]
private lemma left
  [IntegerRing Z]
  {a b : Z} :
-- imply
  b + a - b = a := by
-- proof
  have := IntegerRing.add_sub_cancel a b
  rwa [Add.comm] at this


@[path]
private lemma main
  [IntegerRing Z]
  {a b : Z} :
-- imply
  a + b - b = a := by
-- proof
  apply IntegerRing.add_sub_cancel


-- created on 2024-11-27
-- updated on 2025-10-10
