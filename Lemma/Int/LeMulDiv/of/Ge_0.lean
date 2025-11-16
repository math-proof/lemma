import Lemma.Int.Mod.ge.Zero.of.Ne_0
import Lemma.Nat.EqAddMulDiv
open Nat Int


@[main]
private lemma main
-- given
  (h : n ≥ 0)
  (d : ℤ) :
-- imply
  n / d * d ≤ n := by
-- proof
  if h_d : d = 0 then
    rw [h_d]
    norm_num
    assumption
  else
    have h₁ := Mod.ge.Zero.of.Ne_0 h_d n
    have h₀ := EqAddMulDiv (n := n) (d := d)
    linarith


-- created on 2025-03-29
