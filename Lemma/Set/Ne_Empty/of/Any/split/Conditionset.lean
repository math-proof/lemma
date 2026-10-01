import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {S : Set ℂ}
  {p : ℂ → Prop}
-- given
  (h : ∃ x ∈ S, p x) :
-- imply
  {x | x ∈ S ∧ p x} ≠ ∅ := by
-- proof
  obtain ⟨x, hx, hp⟩ := h
  exact Set.nonempty_iff_ne_empty.mp ⟨x, hx, hp⟩


-- created on 2020-11-07
