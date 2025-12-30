import Lemma.Bool.Any_Not.of.NotAll
open Bool


@[main, comm, mp, mpr]
private lemma main
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


-- created on 2025-12-30
