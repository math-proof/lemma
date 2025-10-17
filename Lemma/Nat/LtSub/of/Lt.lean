import Lemma.Nat.Ge_Add.of.GeSub.Ge
import Lemma.Nat.Sub.eq.Zero.of.Lt
open Nat


@[main]
private lemma main
  {j n : ℕ}
-- given
  (h : j < n) 
  (i : ℕ):
-- imply
  j - i < n := by
-- proof
  by_cases h_le : j ≥ i
  ·
    by_contra h
    simp at h
    have := Ge_Add.of.GeSub.Ge h_le h
    linarith
  ·
    simp at h_le
    have h := Sub.eq.Zero.of.Lt h_le
    rw [h]
    linarith


-- created on 2025-06-21
