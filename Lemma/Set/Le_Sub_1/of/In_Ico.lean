import Lemma.Set.Lt.of.In_Ico
import Lemma.Algebra.Le_Sub_1.of.Lt
open Set Algebra


@[main]
private lemma main
  [IntegerRing α]
  {x a b : α}
-- given
  (h : x ∈ Ico a b) :
-- imply
  x ≤ b - 1 := by
-- proof
  have h := Lt.of.In_Ico h
  apply Le_Sub_1.of.Lt h


-- created on 2025-10-01
