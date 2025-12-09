import Lemma.Nat.Mul
import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import Lemma.Rat.MulDivS.eq.DivMulS
open Nat Rat


@[main]
private lemma main
  [Field α]
  {a : α}
-- given
  (h : a ≠ 0)
  (n d : α) :
-- imply
  (n / a) * (a / d) = n / d := by
-- proof
  rw [MulDivS.eq.DivMulS]
  rw [Mul.comm (a := a)]
  apply DivMulS.eq.Div.of.Ne_0 h


-- created on 2025-12-09
