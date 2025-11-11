import Lemma.Int.LtSubS.of.Lt
open Int


@[main, comm 1]
private lemma left
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a + b < c) :
-- imply
  b < c - a := by
-- proof
  have h := LtSubS.of.Lt h a
  simp at h
  exact h


@[main, comm 1]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a + b < c) :
-- imply
  a < c - b := by
-- proof
  have h := LtSubS.of.Lt h b
  simp at h
  exact h


-- created on 2024-11-27
-- updated on 2025-10-10
