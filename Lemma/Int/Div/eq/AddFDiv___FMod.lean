import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Int.EqAdd_Sub
import Lemma.Int.FMod.eq.Sub_MulFDiv
open Int Nat Rat


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n / (d : ℚ) = (n // d : ℤ) + (n.fmod d : ℤ) / (d : ℚ) := by
-- proof
  have h_Eq := FMod.eq.Sub_MulFDiv (n := n) (d := d)
  rw [h_Eq]
  simp
  rw [DivSub.eq.SubDivS]
  by_cases h : d = 0
  rw [h]
  norm_num
  rw [EqDivMul.of.Ne_0 (by simp [h] : (d : ℚ) ≠ 0)]
  rw [EqAdd_Sub]


-- created on 2025-03-21
