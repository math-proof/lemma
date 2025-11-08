import Lemma.Int.Div.eq.AddFDiv___FMod
import Lemma.Nat.Add
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Int.DivFMod.lt.One
open Nat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {n d : ℤ} :
-- imply
  n / (d : α) < 1 + n // d := by
-- proof
  rw [Div.eq.AddFDiv___FMod n d]
  rw [Add.comm]
  apply LtAddS.of.Lt (a := (n // d : α))
  apply DivFMod.lt.One


-- created on 2025-03-28
-- updated on 2025-03-29
