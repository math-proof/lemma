import Lemma.Int.DivSub1Sign_2.eq.Zero.of.Ge_0
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
open Int Nat Slice


@[main]
private lemma main
  {i : ℤ}
-- given
  (n : ℕ)
  (h : i ≥ 0) :
-- imply
  Add_Mul_DivSub1Sign_2 n i = i := by
-- proof
  have := EqAdd_Mul_DivSub1Sign_2 n i.toNat
  rwa [EqToNat.of.Ge_0 h] at this


-- created on 2026-08-07
