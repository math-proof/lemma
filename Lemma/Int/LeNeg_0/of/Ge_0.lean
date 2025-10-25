import Lemma.Int.GeSubS.of.Ge
import Lemma.Int.Sub.eq.Zero
import Lemma.Int.Sub0.eq.Neg
open Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a : α}
-- given
  (h : a ≥ 0) :
-- imply
  -a ≤ 0 := by
-- proof
  have h := GeSubS.of.Ge h a
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


-- created on 2024-11-29
