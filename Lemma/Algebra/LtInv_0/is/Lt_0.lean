import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [LinearOrderedField α]
  (x : α) :
-- imply
  x⁻¹ < 0 ↔ x < 0 := by
-- proof
  simp_all


-- created on 2025-03-30
