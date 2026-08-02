import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Int.Ge0Sub.is.Le
import Lemma.Int.GeMulFDiv.of.Lt_0
open Int


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d < 0)
  (n : ℤ) :
-- imply
  n.fmod d ≤ 0 := by
-- proof
  have := FMod.eq.Sub_MulFDiv (n := n) (d := d)
  rw [this]
  apply Ge0Sub.of.Le
  apply GeMulFDiv.of.Lt_0 h


-- created on 2025-03-21
