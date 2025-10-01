import Lemma.Logic.Ne.is.NotEq
import Lemma.Algebra.NeDivS.of.Ne.Ne_0
open Logic Algebra


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
  by_cases h_d : d = 0
  · 
    left
    assumption
  · 
    simp [h_d]
    apply NotEq.of.Ne
    have h_d := Ne.of.NotEq h_d
    apply NeDivS.of.Ne.Ne_0 h h_d


-- created on 2025-10-01
