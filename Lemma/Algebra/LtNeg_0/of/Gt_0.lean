import Lemma.Algebra.GtSubS.of.Gt
import Lemma.Int.Sub.eq.Zero
import Lemma.Algebra.Sub0.eq.Neg
open Algebra Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a : α}
-- given
  (h : a > 0) :
-- imply
  -a < 0 := by
-- proof
  have h := GtSubS.of.Gt h a
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


-- created on 2024-11-29
