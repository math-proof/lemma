import Lemma.Int.Div.eq.AddFDiv___FMod
import Lemma.Int.DivFMod.ge.Zero
import Lemma.Algebra.Ge.of.Eq_Add.Ge_0
open Algebra Int


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n / (d : ℚ) ≥ (n // d : ℤ) := by
-- proof
  have h_Eq := Div.eq.AddFDiv___FMod (n := n) (d := d)
  have := DivFMod.ge.Zero (n := n) (d := d)
  apply Ge.of.Eq_Add.Ge_0 h_Eq this


-- created on 2025-03-21
-- updated on 2025-03-28
