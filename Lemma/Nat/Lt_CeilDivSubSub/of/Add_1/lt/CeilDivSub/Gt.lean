import Lemma.Nat.Lt_CeilDivSub_Add.of.Add_1.lt.CeilDivSub
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Nat.Add
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Gt
open Nat Int


@[main]
private lemma main
  {start stop step i : ℕ}
-- given
  (h₀ : start > step)
  (h₁ : i + 1 < ⌈(start - stop : ℚ) / step⌉) :
-- imply
  i < ⌈((start - step : ℕ) - stop : ℚ) / step⌉ := by
-- proof
  rw [CoeSub.eq.SubCoeS.of.Gt]
  rw [SubSub.eq.Sub_Add]
  rw [Add.comm]
  apply Lt_CeilDivSub_Add.of.Add_1.lt.CeilDivSub h₁
  assumption


-- created on 2025-05-28
