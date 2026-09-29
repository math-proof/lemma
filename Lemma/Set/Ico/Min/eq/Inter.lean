import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b c : α} :
-- imply
  Ico a (min b c) = Ico a b ∩ Ico a c := by
-- proof
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ico, lt_min_iff]
  tauto


-- created on 2026-09-27
