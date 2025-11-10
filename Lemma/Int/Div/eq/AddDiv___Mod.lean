import Lemma.Nat.Mod.eq.Sub_MulDiv
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Int.EqAdd_Sub
open Nat Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (n d : ℤ) :
-- imply
  n / (d : α) = (n / d : ℤ) + (n % d : ℤ) / (d : α) := by
-- proof
  have h_Eq := Mod.eq.Sub_MulDiv (n := n) (d := d)
  rw [h_Eq]
  simp
  rw [DivSub.eq.SubDivS]
  if h : d = 0 then
    rw [h]
    norm_num
  else
    rw [EqDivMul.of.Ne_0 (by simp [h] : (d : α) ≠ 0)]
    rw [EqAdd_Sub]


-- created on 2025-03-20
