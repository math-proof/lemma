import Lemma.Bool.Any.is.NotAll_Not
open Bool


@[main, comm]
private lemma main
-- given
  (p : α → Prop) :
-- imply
  (¬∀ x : α, p x) ↔ ∃ x : α, ¬p x := by
-- proof
  rw [Any.is.NotAll_Not]
  simp


-- created on 2024-07-01
