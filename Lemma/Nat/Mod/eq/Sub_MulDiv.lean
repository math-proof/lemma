import Lemma.Nat.Mod.eq.Sub_Mul_Div
import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n d : Z} :
-- imply
  n % d = n - n / d * d := by
-- proof
  rw [Mul.comm]
  apply Mod.eq.Sub_Mul_Div


-- created on 2025-03-16
-- updated on 2026-07-12
