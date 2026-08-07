import Lemma.Int.EqAdd_Mul_DivSub1Sign_2.of.Ge_0
import Lemma.Int.EqToNat.of.Ge_0
open Int Slice


@[main]
private lemma main
  {i : ℤ}
-- given
  (n : ℕ)
  (h : i ≥ 0) :
-- imply
  (Add_Mul_DivSub1Sign_2 n i).toNat = i := by
-- proof
  rw [EqAdd_Mul_DivSub1Sign_2.of.Ge_0 n h, EqToNat.of.Ge_0 h]


-- created on 2026-08-07
