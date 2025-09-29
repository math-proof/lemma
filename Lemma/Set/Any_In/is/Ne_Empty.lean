import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (S : Set α) :
-- imply
  (∃ e : α, e ∈ S) ↔ S ≠ ∅ := by
-- proof
  have := Set.nonempty_iff_ne_empty (s := S)
  simp [Set.Nonempty] at this
  assumption


-- created on 2025-07-19
-- updated on 2025-08-02
