import Lemma.Algebra.Div.ge.Zero.of.Ge_0.Ge_0
import Lemma.Nat.Ge.of.Gt
open Algebra Nat


@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b > 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have := Ge.of.Gt h₁
  apply Div.ge.Zero.of.Ge_0.Ge_0 h₀ this


-- created on 2025-03-30
