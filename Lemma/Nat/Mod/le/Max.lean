import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.LtMod.of.Gt_0
open Nat


@[main]
private lemma main
-- given
  (n d : ℕ) :
-- imply
  n % d ≤ n ⊔ d := by
-- proof
  by_cases h_d : d = 0
  ·
    subst h_d
    simp
  ·
    have h_d := Gt_0.of.Ne_0 h_d
    have := LtMod.of.Gt_0 h_d n
    grind


-- created on 2025-11-03
