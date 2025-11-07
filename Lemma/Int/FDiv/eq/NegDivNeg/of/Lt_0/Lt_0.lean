import sympy.functions.elementary.integers
import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.Int.EqNegNeg
import Lemma.Int.Div_Neg.eq.NegDiv
open Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n < 0)
  (h₁ : d < 0) :
-- imply
  n // d = -(-n / d) := by
-- proof
  unfold Int.fdiv
  match n, d with
  | 0, x =>
    contradiction
  | .ofNat m, .ofNat n =>
    contradiction
  | .ofNat (.succ m), .negSucc n =>
    contradiction
  | .negSucc a, 0 =>
    contradiction
  | .negSucc m, .ofNat (.succ n) =>
    contradiction
  | .negSucc m, .negSucc n =>
    simp
    rw [NegSucc.eq.NegAdd_1]
    rw [Div_Neg.eq.NegDiv]
    rw [EqNegNeg]


-- created on 2025-03-28
-- updated on 2025-03-29
