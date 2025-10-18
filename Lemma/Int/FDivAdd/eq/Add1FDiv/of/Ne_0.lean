import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Rat.DivAdd.eq.Add1Div
import Lemma.Int.CoeAdd.eq.AddCoeS
import Lemma.Algebra.FloorAdd1.eq.Add1Floor
open Algebra Int Rat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≠ 0) :
-- imply
  (d + n) // d = 1 + n // d := by
-- proof
  repeat rw [FDiv.eq.FloorDiv]
  rw [CoeAdd.eq.AddCoeS]
  rw [DivAdd.eq.Add1Div (by simp [h] : (d : ℚ) ≠ 0)]
  -- Apply the property of the floor function for adding an integer
  rw [FloorAdd1.eq.Add1Floor]


-- created on 2025-03-21
-- updated on 2025-10-08
