import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (S : Finset α) :
-- imply
  (∃ e : α, e ∈ S) ↔ S ≠ ∅ := by
-- proof
  have := Finset.nonempty_iff_ne_empty (s := S)
  simp [Finset.Nonempty] at this
  assumption


-- created on 2025-10-08
