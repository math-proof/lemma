import Lemma.Set.InDiv.of.In_Icc.Ge_0
open Set


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h : x ∈ Icc a b)
  (d : ℕ) :
-- imply
  x / d ∈ Icc (a / d) (b / d) := by
-- proof
  apply InDiv.of.In_Icc.Ge_0 h
  simp


-- created on 2025-03-01
