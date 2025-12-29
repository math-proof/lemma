import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
import Lemma.Rat.Lt0Div.is.Lt0Mul
open Rat Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a / b > 0 :=
-- proof
  Lt0Div.of.Lt0Mul (Lt0Mul.of.Gt_0.Gt_0 h₀ h₁)


-- created on 2025-12-28
