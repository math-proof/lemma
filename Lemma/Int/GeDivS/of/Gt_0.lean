import Lemma.Int.Mod.ge.Zero.of.Gt_0
import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Int.Ge.of.Eq_Add.Ge_0
open Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n / (d : α) ≥ (n / d : ℤ) := by
-- proof
  have h_Ge_0 := Mod.ge.Zero.of.Gt_0 (n := n) h
  have h_Ge_0 : (n % d : ℤ) ≥ (0 : α) := by simp [h_Ge_0]
  have h_GeDivS := GeDivS.of.Ge.Gt_0 h_Ge_0 (by simp [h] : (d : α) > 0)
  norm_num at h_GeDivS
  apply Ge.of.Eq_Add.Ge_0 _ h_GeDivS
  apply Div.eq.AddDiv___Mod n d


-- created on 2025-03-20
