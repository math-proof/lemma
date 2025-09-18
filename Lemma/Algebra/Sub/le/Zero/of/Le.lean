import Lemma.Algebra.Sub.eq.Zero
import Lemma.Algebra.LeSubS.is.Le
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  x - y ≤ 0 := by
-- proof
  have := LeSubS.of.Le y h
  rw [Sub.eq.Zero] at this
  assumption


-- created on 2025-03-15
