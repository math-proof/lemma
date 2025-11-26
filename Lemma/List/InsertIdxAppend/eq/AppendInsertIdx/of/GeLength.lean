import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length ≥ i)
  (x : α) :
-- imply
  (a ++ b).insertIdx i x = a.insertIdx i x ++ b := by
-- proof
  induction a generalizing i with
  | nil =>
    simp at h
    simp [h]
  | cons head tail ih =>
    cases i <;>
      simp_all


-- created on 2025-11-26
