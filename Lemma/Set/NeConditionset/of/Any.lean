import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {p : ℝ → Prop}
-- given
  (h : ∃ e ∈ S, p e) :
-- imply
  {e | e ∈ S ∧ p e} ≠ ∅ := by
-- proof
  obtain ⟨e, he, hp⟩ := h
  exact Set.nonempty_iff_ne_empty.mp ⟨e, he, hp⟩


-- created on 2021-08-03
