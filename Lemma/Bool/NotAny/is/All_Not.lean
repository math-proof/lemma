import Lemma.Bool.All.is.NotAny_Not
open Bool


@[main, comm, mp, mpr]
private lemma main
-- given
  (p : α → Prop) :
-- imply
  (¬∃ x : α, p x) ↔ ∀ x : α, ¬p x := by
-- proof
  rw [All.is.NotAny_Not]
  simp


-- created on 2024-07-01
