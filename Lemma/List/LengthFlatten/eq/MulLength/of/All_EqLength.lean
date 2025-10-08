import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Nat.Add
open Algebra Nat


@[main]
private lemma main
  {n : ℕ}
  {v : List (List α)}
-- given
  (h : ∀ l ∈ v, l.length = n) :
-- imply
  v.flatten.length = v.length * n := by
-- proof
  induction v with
  | nil =>
    simp_all
  | cons v₀ v ih =>
    simp_all
    rw [MulAdd.eq.AddMulS]
    simp
    rw [Add.comm]


-- created on 2025-06-28
