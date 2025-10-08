import Lemma.Nat.Eq.of.Le.Ge
open Nat


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h₀ : b ≤ a)
  (h₁ : a ≤ b) :
-- imply
  a = b :=
-- proof
  Eq.of.Le.Ge h₁ h₀


-- created on 2025-05-17
