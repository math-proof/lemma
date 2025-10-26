import Lemma.Algebra.NeAddS.of.Ne
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x a b: α}
-- given
  (h : x - b ≠ a) :
-- imply
  x ≠ a + b := by
-- proof
  have h := NeAddS.of.Ne h b
  simp at h
  exact h


-- created on 2024-11-27
