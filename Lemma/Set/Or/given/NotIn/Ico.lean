import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b e : ℤ}
-- given
  (h : e < a ∨ e ≥ b) :
-- imply
  e ∉ Set.Ico a b := by
-- proof
  intro hx
  obtain ⟨hea, heb⟩ := hx
  obtain hlt | hge := h
  · omega
  · omega


-- created on 2022-01-28
