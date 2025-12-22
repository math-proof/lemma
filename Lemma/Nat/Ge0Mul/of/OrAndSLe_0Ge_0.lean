import Lemma.Int.Ge0Mul.of.Le_0.Ge_0
import Lemma.Int.Le_0.of.Ge_0.Le_0
open Int


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α] [MulPosStrictMono α]
  {x y : α}
-- given
  (h : x ≤ 0 ∧ y ≥ 0 ∨ y ≤ 0 ∧ x ≥ 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  cases h with
  | inl h =>
    apply Ge0Mul.of.Le_0.Ge_0 h.left h.right
  | inr h =>
    apply Le_0.of.Ge_0.Le_0 h.right h.left


-- created on 2025-03-29
