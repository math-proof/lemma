import Lemma.Nat.LtVal
open Nat


@[main]
private lemma main
-- given
  (h : n = m)
  (i : Fin n) :
-- imply
  have h_i := LtVal i
  have h_i' : i < m := by
    simp [h] at h_i
    assumption
  HEq i (⟨i, h_i'⟩ : Fin m) := by
-- proof
  aesop


-- created on 2025-07-14
