import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℂ}
  {p : ℂ → Prop}
-- given
  (h : {x | x ∈ S ∧ p x} ≠ ∅) :
-- imply
  ∃ x ∈ S, p x := by
-- proof
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
  exact ⟨x, hx.1, hx.2⟩


-- created on 2020-11-07
