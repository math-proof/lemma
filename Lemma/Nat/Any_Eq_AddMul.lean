import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
open Nat


@[main]
private lemma main
  {m n : ℕ}
-- given
  (t : Fin (m * n)) :
-- imply
  ∃ i : Fin m, ∃ j : Fin n, t = i.val * n + j := by
-- proof
  let ⟨t, h_t⟩ := t
  obtain ⟨i, hi, j, hj, h_eq⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  let i' : Fin m := ⟨i, hi⟩
  have h_i : i' = i := rfl
  let j' : Fin n := ⟨j, hj⟩
  have h_j : j' = j := rfl
  use i', j'


@[main]
private lemma comm'
  {m n : ℕ}
-- given
  (t : Fin (m * n)) :
-- imply
  ∃ i : Fin m, ∃ j : Fin n, t = n * i + j := by
-- proof
  simp [mul_comm (a := n)]
  apply main

-- created on 2025-07-03
