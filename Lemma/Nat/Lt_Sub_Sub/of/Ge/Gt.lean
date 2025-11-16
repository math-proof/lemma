import Lemma.Nat.SubAdd.eq.Sub_Sub.of.Ge
open Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h₀ : b > c)
  (h₁ : c ≥ a) :
-- imply
  a < b - (c - a) := by
-- proof
  rw [Sub_Sub.eq.SubAdd.of.Ge h₁]
  omega


-- created on 2025-11-16
