import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Int.Mod.ge.Zero.of.Lt_0
import Lemma.Rat.LeDivS.of.Ge.Lt_0
import Lemma.Int.Le.of.Eq_Add.Le_0
open Int Rat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n / (d : ℚ) ≤ (n / d : ℤ) := by
-- proof
  have h_Ge_0 := Mod.ge.Zero.of.Lt_0 (n := n) h
  have h_Ge_0 : (n % d : ℤ) ≥ (0 : ℚ) := by
    simp [h_Ge_0]
  have h_Eq := Div.eq.AddDiv___Mod (n := n) (d := d)
  have h_LeDivS := LeDivS.of.Ge.Lt_0 h_Ge_0 (by simp [h] : (d : ℚ) < 0)
  norm_num at h_LeDivS
  exact Le.of.Eq_Add.Le_0 h_Eq h_LeDivS


-- created on 2025-03-20
