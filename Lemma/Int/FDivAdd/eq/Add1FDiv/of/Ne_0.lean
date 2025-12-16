import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Rat.DivAdd.eq.Add1Div.of.Ne_0
import Lemma.Int.CoeAdd.eq.AddCoeS
import Lemma.Rat.FloorAdd1.eq.Add1Floor
open Int Rat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≠ 0) :
-- imply
  (d + n) // d = 1 + n // d := by
-- proof
  repeat rw [FDiv.eq.FloorDiv (α := ℚ)]
  rw [CoeAdd.eq.AddCoeS]
  rw [DivAdd.eq.Add1Div.of.Ne_0 (by simp [h] : (d : ℚ) ≠ 0)]
  rw [FloorAdd1.eq.Add1Floor]


-- created on 2025-03-21
-- updated on 2025-10-08
