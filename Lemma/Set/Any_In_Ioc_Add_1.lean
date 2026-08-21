import sympy.sets.sets
import Lemma.Set.In_IocCeil
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  ∃ k : ℤ, x ∈ Ioc (k : α) (k + 1 : α) := by
-- proof
  refine ⟨⌈x⌉ - 1, ?_⟩
  simpa [Int.cast_sub, Int.cast_add] using In_IocCeil (x := x)


-- created on 2018-10-29
-- updated on 2026-08-20
