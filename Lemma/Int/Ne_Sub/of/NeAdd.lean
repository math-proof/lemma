import Lemma.Int.NeSubS.of.Ne
open Int


@[main]
private lemma left
  [AddCommGroup α]
  {x a b : α}
-- given
  (h : b + x ≠ a) :
-- imply
  x ≠ a - b := by
-- proof
  have h := NeSubS.of.Ne h b
  simp at h
  exact h


@[main]
private lemma main
  [AddGroup α]
  {x a b : α}
-- given
  (h : x + b ≠ a) :
-- imply
  x ≠ a - b := by
-- proof
  have h := NeSubS.of.Ne h b
  simp at h
  exact h


-- created on 2024-11-27
-- updated on 2025-06-11
