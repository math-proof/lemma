import sympy.Basic


@[main]
private lemma subst
  [Decidable p]
  [Decidable q]
-- given
  (h : p ↔ q) :
-- imply
  (if p then
    a
  else
    b) = if q then
    a
  else
    b := by
-- proof
  simp [h]


-- created on 2025-06-06
