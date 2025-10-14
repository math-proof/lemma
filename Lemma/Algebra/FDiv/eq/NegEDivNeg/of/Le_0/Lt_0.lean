import sympy.functions.elementary.integers
import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.Int.EqNegNeg
import Lemma.Algebra.EDiv_Neg.eq.NegEDiv
open Algebra Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n ≤ 0)
  (h₁ : d < 0) :
-- imply
  n // d = -(-n / d) := by
-- proof
  unfold Int.fdiv
  match n, d with
  | 0, _ =>
    simp
  | Int.ofNat _, Int.ofNat _ =>
    contradiction
  | Int.ofNat (.succ _), Int.negSucc _ =>
    contradiction
  | Int.negSucc _, 0 =>
    contradiction
  | Int.negSucc _, Int.ofNat (.succ _) =>
    contradiction
  | Int.negSucc n, Int.negSucc d =>
    simp
    repeat rw [NegSucc.eq.NegAdd_1]
    rw [EqNegNeg]
    rw [EDiv_Neg.eq.NegEDiv]
    rw [EqNegNeg]


-- created on 2025-03-27
-- updated on 2025-03-28
