import Lemma.Bool.Ne.is.NotEq
import Lemma.Rat.NeDivS.of.Ne.Ne_0
open Bool Rat


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
    apply NotEq.of.Ne
    have h_d := Ne.of.NotEq h_d
    apply NeDivS.of.Ne.Ne_0 h h_d


-- created on 2025-10-01
