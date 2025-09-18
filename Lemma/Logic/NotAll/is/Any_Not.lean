import Lemma.Logic.Any.is.NotAll_Not
open Logic


@[main, comm]
private lemma fin
  (s : Finset ι)
  (p : ι → Prop) :
-- imply
  (¬∀ x : s, p x) ↔ ∃ x : s, ¬p x := by
-- proof
  push_neg
  rfl


@[main, comm]
private lemma main
  (p : α → Prop) :
-- imply
  (¬∀ x : α, p x) ↔ ∃ x : α, ¬p x := by
-- proof
  rw [Any.is.NotAll_Not]
  simp


-- created on 2024-07-01
