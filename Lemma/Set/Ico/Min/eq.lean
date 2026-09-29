import sympy.sets.sets
import sympy.Basic


@[main]
private lemma union
  [LinearOrder α]
  {a b c : α} :
-- imply
  Ico (min b c) a = Ico b a ∪ Ico c a := by
-- proof
  ext x
  simp only [Set.mem_union, Set.mem_Ico, min_le_iff]
  tauto


-- created on 2026-09-27
