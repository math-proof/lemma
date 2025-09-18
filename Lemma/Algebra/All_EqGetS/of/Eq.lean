import stdlib.SEq
import stdlib.List.Vector


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h : a ≃ b) :
-- imply
  ∀ i : Fin n, a.get i = b.get ⟨i, by rw [← h.left]; simp⟩ := by
-- proof
  let ⟨h_n, h⟩ := h
  intro i
  subst h_n
  simp [HEq.eq h]


-- created on 2025-07-24
