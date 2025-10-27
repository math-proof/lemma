import Lemma.Int.Mod.ge.Zero.of.Ne_0
import Lemma.Nat.Eq_AddMulDiv___Mod
open Nat Int


@[main]
private lemma main
-- given
  (h : n ≥ 0)
  (d : ℤ) :
-- imply
  n / d * d ≤ n := by
-- proof
  by_cases h_d : d = 0
  ·
    rw [h_d]
    norm_num
    assumption
  ·
  -- The remainder (n % d) is non-negative
    have h₁ := Mod.ge.Zero.of.Ne_0 h_d n
  -- Use the division algorithm to express n as (n / d) * d + (n % d)
    have h₀ := Eq_AddMulDiv___Mod (n := n) (d := d)
  -- Since (n % d) is non-negative, (n / d) * d ≤ n
    linarith


-- created on 2025-03-29
