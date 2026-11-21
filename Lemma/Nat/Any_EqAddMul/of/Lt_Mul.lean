import Lemma.Nat.EqAddMulDiv
open Nat


@[path]
private lemma left
  {k n m : ℕ}
-- given
  (h : k < n * m) :
-- imply
  ∃ (i : Fin m) (j : Fin n), i * n + j = k := by
-- proof
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    simp [hn] at h
  use ⟨k / n, Nat.div_lt_of_lt_mul h⟩, ⟨k % n, Nat.mod_lt k hn⟩
  apply EqAddMulDiv

@[path]
private lemma main
  {k n m : ℕ}
-- given
  (h : k < m * n) :
-- imply
  ∃ (i : Fin m) (j : Fin n), i * n + j = k := by
-- proof
  rw [Nat.mul_comm] at h
  apply left h


-- created on 2025-05-29
-- updated on 2026-11-21
