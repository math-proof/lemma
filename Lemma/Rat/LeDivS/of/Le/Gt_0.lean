import Lemma.Nat.Ge.of.Gt
import Lemma.Rat.LeDivS.of.Le.Ge_0
open Nat Rat


@[main, comm 2]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x > 0) :
-- imply
  a / x ≤ b / x := by
-- proof
  apply LeDivS.of.Le.Ge_0 h₀
  apply Ge.of.Gt h₁


-- created on 2024-11-25
-- updated on 2025-12-11
