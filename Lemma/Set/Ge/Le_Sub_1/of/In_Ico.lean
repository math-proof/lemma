import Lemma.Set.Le_Sub_1.of.In_Ico
import Lemma.Set.Ge.of.In_Ico
open Set


@[main]
private lemma main
  [IntegerRing α]
  {x a b : α}
-- given
  (h : x ∈ Ico a b) :
-- imply
  x ≥ a ∧ x ≤ b - 1 := by
-- proof
  constructor
  · 
    apply Ge.of.In_Ico h
  · 
    apply Le_Sub_1.of.In_Ico h


-- created on 2025-10-01
