import Lemma.Int.LeMulS.of.Ge_0.Le
open Int


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : a ≥ b) :
-- imply
  x * a ≥ x * b :=
-- proof
  LeMulS.of.Ge_0.Le h₀ h₁


-- created on 2024-07-01
