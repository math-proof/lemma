import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqAddS.is.Eq
open Nat


@[main]
private lemma main
  {n i j i' j' : ℕ}
-- given
  (h_j : j < n)
  (h_j' : j' < n)
  (h_eq : i' * n + j' = i * n + j) :
-- imply
  i' = i ∧ j' = j := by
-- proof
  have h_mod := congr_arg (· % n) h_eq
  simp at h_mod
  repeat rw [EqMod.of.Lt (by assumption)] at h_mod
  aesop


-- created on 2025-10-17
