import Lemma.Algebra.Div.eq.AddFDiv___FMod
import Lemma.Algebra.Add
import Lemma.Algebra.LtAddS.is.Lt
import Lemma.Algebra.DivFMod.lt.One
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n / (d : ℚ) < 1 + n // d := by
-- proof
  -- Use the fact that the floor of n/d is less than or equal to n/d
  have h_Eq := Div.eq.AddFDiv___FMod (n := n) (d := d)
  rw [h_Eq]
  rw [Add.comm]
  apply LtAddS.of.Lt (a := (n // d : ℚ))
  apply DivFMod.lt.One


-- created on 2025-03-28
-- updated on 2025-03-29
