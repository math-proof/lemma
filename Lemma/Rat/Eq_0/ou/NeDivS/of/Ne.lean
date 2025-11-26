import Lemma.Bool.Ne.is.NotEq
open Bool


@[main]
private lemma main
  [GroupWithZero α]
  {x y : α}
-- given
  (h : x ≠ y)
  (d : α) :
-- imply
  d = 0 ∨ x / d ≠ y / d := by
-- proof
  if h_d : d = 0 then
    left
    assumption
  else
    simp [h_d]
    apply NotEq.of.Ne h


-- created on 2025-10-01
-- updated on 2025-11-26
