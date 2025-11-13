import Lemma.Int.LeMulS.of.Le.Ge_0
open Int


@[main, comm 1]
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


@[main, comm 1]
private lemma left
  {a b : ℕ}
-- given
  (h : a ≤ b)
  (k : ℕ) :
-- imply
  k * a ≤ k * b := by
-- proof
  cases k <;>
    simp_all


-- created on 2025-07-06
