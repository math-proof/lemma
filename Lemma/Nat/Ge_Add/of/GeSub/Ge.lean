import Lemma.Nat.Le_Sub.is.LeAdd.of.Le
open Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h₀ : c ≥ b)
  (h₁ : c - b ≥ a) :
-- imply
  c ≥ a + b :=
-- proof
  LeAdd.of.Le_Sub.Le h₀ h₁


@[main]
private lemma left
  {a b c : ℕ}
-- given
  (h₀ : c ≥ a)
  (h₁ : c - a ≥ b) :
-- imply
  c ≥ a + b :=
-- proof
  LeAdd.of.Le_Sub.Le.left h₀ h₁


-- created on 2025-06-21
