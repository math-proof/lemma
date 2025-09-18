import Lemma.Algebra.GeSubS.of.Ge
import Lemma.Algebra.Sub.eq.Zero
import Lemma.Algebra.Sub0.eq.Neg
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
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
