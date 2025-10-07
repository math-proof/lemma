import Lemma.Logic.Any_Not.of.NotAll
open Logic


@[main, comm, mp, mpr]
private lemma fin
-- given
  (s : Finset ι)
  (p : ι → Prop) :
-- imply
  (∃ x : s, p x) ↔ ¬∀ x : s, ¬p x := by
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
    let ⟨a, ha, pa⟩ := h
    use ⟨a, ha⟩


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
