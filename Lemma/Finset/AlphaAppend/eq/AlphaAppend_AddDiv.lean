import sympy.concrete.continued_fraction
import sympy.Basic
import Lemma.Finset.Alpha_Cons.eq.Add_DivAlpha
open Finset Continuant


@[main]
private lemma main
  [Field R]
-- given
  (l : List R)
  (a b : R) :
-- imply
  alpha (l ++ [a, b]) = alpha (l ++ [a + 1 / b]) := by
-- proof
  induction l with
  | nil => simp [alpha]
  | cons c l ih =>
    rw [List.cons_append, List.cons_append, Alpha_Cons.eq.Add_DivAlpha _ (by simp), Alpha_Cons.eq.Add_DivAlpha _ (by simp), ih]


-- created on 2026-10-07
