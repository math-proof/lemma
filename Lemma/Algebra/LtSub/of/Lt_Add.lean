import Lemma.Algebra.LtSubS.of.Lt
open Algebra


@[main]
private lemma left
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : c < a + b) :
-- imply
  c - a < b := by
-- proof
  have h := LtSubS.of.Lt h a
  simp at h
  exact h


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : c < a + b) :
-- imply
  c - b < a := by
-- proof
  have h := LtSubS.of.Lt h b
  simp at h
  exact h


-- created on 2024-11-27
-- updated on 2025-05-24
