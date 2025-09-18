import Lemma.Logic.Any.is.NotAll_Not
open Logic


@[main, comm, mpr]
private lemma main
-- given
  (p : α → Prop) :
-- imply
  (∀ x : α, p x) ↔ ¬∃ x : α, ¬p x := by
-- proof
  rw [Any.is.NotAll_Not]
  simp


-- created on 2024-07-01
