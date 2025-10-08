import sympy.core.relational
import Lemma.Int.FloorAdd.eq.Add_Floor
open Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x y : α}
-- given
  (h : ⌊x⌋ = x) :
-- imply
  ⌊x + y⌋ = x + ⌊y⌋ := by
-- proof
  denote h_Eq : d = ⌊x⌋
  rw [← h_Eq] at h
  rw [← h]
  norm_cast
  apply FloorAdd.eq.Add_Floor


-- created on 2025-03-16
