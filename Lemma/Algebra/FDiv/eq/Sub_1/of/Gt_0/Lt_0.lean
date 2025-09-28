import sympy.functions.elementary.integers
import Lemma.Algebra.NegSucc.eq.NegAdd_1
import Lemma.Algebra.NegAdd.eq.SubNeg
import Lemma.Algebra.EDiv_Neg.eq.NegEDiv
import Lemma.Algebra.Sub.eq.Add_Neg
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n > 0)
  (h₁ : d < 0) :
-- imply
  n // d = (n - 1) / d - 1 := by
-- proof
  unfold Int.fdiv
  match n, d with
  | 0, x =>
    contradiction
  | Int.ofNat m, Int.ofNat n =>
    contradiction
  | Int.ofNat (.succ n), Int.negSucc d =>
    simp
    repeat rw [NegSucc.eq.NegAdd_1]
    ring_nf
    rw [SubNeg.eq.NegAdd (b := (d : ℤ))]
    rw [EDiv_Neg.eq.NegEDiv]
    rw [Add_Neg.eq.Sub]
    norm_cast
  | Int.negSucc a, 0 =>
    contradiction
  | Int.negSucc m, Int.ofNat (.succ n) =>
    contradiction
  | Int.negSucc m, Int.negSucc n =>
    contradiction


-- created on 2025-03-27
-- updated on 2025-03-28
