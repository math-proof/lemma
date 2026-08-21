import Lemma.Nat.Eq.of.Le.Le
open Nat


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h₀ : b ≥ a)
  (h₁ : a ≥ b) :
-- imply
  a = b := 
-- proof
  Eq.of.Le.Le h₀ h₁


-- created on 2025-05-17
