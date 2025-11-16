import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.LtMod.of.Ne_0
open Nat


@[main]
private lemma main
-- given
  (n k : ℕ) :
-- imply
  (k % n) / n = 0 := by
-- proof
  if h_n : n = 0 then
    subst h_n
    simp
  else
    apply Div.eq.Zero.of.Lt
    apply LtMod.of.Ne_0 h_n


-- created on 2025-11-16
