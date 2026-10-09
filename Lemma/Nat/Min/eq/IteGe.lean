import Lemma.Nat.Min
import Lemma.Nat.Min.eq.IteLe
open Nat


@[path]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a ≥ b then
    b
  else
    a := by
-- proof
  rw [Min.comm]
  rw [Min.eq.IteLe]


-- created on 2025-05-07
