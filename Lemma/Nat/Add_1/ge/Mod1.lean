import Lemma.Nat.Ge1Mod1
open Nat


@[main]
private lemma main
-- given
  (m : ℕ)
  (n : ℕ := m) :
-- imply
  m + 1 ≥ 1 % n := by
-- proof
  linarith [Ge1Mod1 n]


-- created on 2025-10-30
