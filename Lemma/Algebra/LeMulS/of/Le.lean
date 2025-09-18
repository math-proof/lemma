import Lemma.Algebra.LeMulS.of.Le.Ge_0
open Algebra


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a ≤ b)
  (x : ℕ) :
-- imply
  a * x ≤ b * x := by
-- proof
  apply LeMulS.of.Le.Ge_0 <;>
    linarith


-- created on 2025-07-06
