import Lemma.Algebra.EqAddS.is.Eq
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x y : α}
-- given
  (h : x ≠ y)
  (d : α) :
-- imply
  x - d ≠ y - d := by
-- proof
  intro h'
  have h' := EqAddS.of.Eq d h'
  simp at h'
  exact h h'


-- created on 2024-11-27
