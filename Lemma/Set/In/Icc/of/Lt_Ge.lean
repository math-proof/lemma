import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (hlt : x < b)
  (hge : a ≤ x) :
-- imply
  x ∈ Ico a b :=
-- proof
  ⟨hge, hlt⟩


-- created on 2026-09-26
