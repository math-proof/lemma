import Lemma.Int.Div.eq.AddFDiv___FMod
import Lemma.Int.DivFMod.ge.Zero
import Lemma.Int.Ge.of.Eq_Add.Ge_0
open Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {n d : ℤ} :
-- imply
  n / (d : α) ≥ (n // d : ℤ) := by
-- proof
  apply Ge.of.Eq_Add.Ge_0
  .
    apply Div.eq.AddFDiv___FMod
  .
    apply DivFMod.ge.Zero


-- created on 2025-03-21
-- updated on 2025-03-28
