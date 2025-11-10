import Lemma.Int.EqToNat
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Rat.EqToNatCeilDivSubMul.of.Lt
open Int Nat Rat


@[main]
private lemma main
  {i : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  (⟨i, m * n, n⟩ : Slice).length (m * n) = m := by
-- proof
  unfold Slice.length
  simp [EqAdd_Mul_DivSub1Sign_2]
  repeat rw [MulCoeS.eq.CoeMul]
  rw [EqAdd_Mul_DivSub1Sign_2]
  rw [EqToNat]
  simp
  rwa [EqToNatCeilDivSubMul.of.Lt]


-- created on 2025-11-09
