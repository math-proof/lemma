import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {n : ℕ}
  {s : List (List α)}
-- given
  (h : ∀ l ∈ s, l.length = n) :
-- imply
  s.flatten.length = s.length * n := by
-- proof
  induction s with
  | nil =>
    simp_all
  | cons s₀ s ih =>
    simp_all
    rw [MulAdd.eq.AddMulS]
    simp
    rw [Add.comm]


-- created on 2025-06-28
