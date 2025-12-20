import Lemma.Nat.Mul
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.MulDivS.eq.DivMulS
open Nat Rat


@[main]
private lemma main
  [Semifield α]
  {a b : α}
-- given
  (h_a : a ≠ 0)
  (h_b : b ≠ 0) :
-- imply
  (a / b) * (b / a) = 1 := by
-- proof
  rw [MulDivS.eq.DivMulS]
  rw [Mul.comm]
  rw [Div.eq.One.of.Ne_0]
  apply Mul.ne.Zero.of.Ne_0.Ne_0 h_b h_a


-- created on 2025-12-20
