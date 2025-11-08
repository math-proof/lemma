import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Int.Mod.ge.Zero.of.Lt_0
import Lemma.Rat.LeDivS.of.Ge.Lt_0
import Lemma.Int.Le.of.Eq_Add.Le_0
open Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n / (d : α) ≤ (n / d : ℤ) := by
-- proof
  have h_Ge_0 := Mod.ge.Zero.of.Lt_0 (n := n) h
  have h_Ge_0 : (n % d : ℤ) ≥ (0 : α) := by
    simp [h_Ge_0]
  have h_LeDivS := LeDivS.of.Ge.Lt_0 h_Ge_0 (by simp [h] : (d : α) < 0)
  norm_num at h_LeDivS
  apply Le.of.Eq_Add.Le_0 _ h_LeDivS
  apply Div.eq.AddDiv___Mod n d


-- created on 2025-03-20
