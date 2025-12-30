import Lemma.Bool.Any_Not.of.NotAll
open Bool


@[main, comm, mp, mpr]
private lemma main
-- given
  (p : α → Prop) :
-- imply
  (∃ x : α, p x) ↔ ¬∀ x : α, ¬p x := by
-- proof
  constructor <;>
    intro h
  ·
    intro h_All
    let ⟨x, h⟩ := h
    have h := h_All x
    contradiction
  ·
    have h := Any_Not.of.NotAll h
    simp at h
    exact h


-- created on 2024-07-01
