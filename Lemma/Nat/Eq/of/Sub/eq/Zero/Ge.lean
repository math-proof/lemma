import Lemma.Nat.Le.of.Sub.eq.Zero
import Lemma.Nat.Eq.of.Le.Le
open Nat


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h_ge : a ≥ b)
  (h_eq : a - b = 0) :
-- imply
  a = b := by
-- proof
  have := Le.of.Sub.eq.Zero h_eq
  apply Eq.of.Le.Le this h_ge


-- created on 2025-04-11
