import sympy.functions.elementary.integers
import Lemma.Int.Ceil.eq.FloorDivSub_Sign
open Int


@[path]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ}
-- given
  (h : d ≠ 0) :
-- imply
  ⌈n / (d : α)⌉ - 1 = ⌊(n - sign d) / (d : α)⌋ := by
-- proof
  have hd : (d : α) ≠ 0 := by exact_mod_cast h
  rw [Ceil.eq.FloorDivSub_Sign (α := α) n d, add_sub_assoc, add_div, div_self hd, add_comm, Int.floor_add_one, add_sub_cancel_right]


-- created on 2018-08-11
