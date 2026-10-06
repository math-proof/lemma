import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
-- given
  (h : x ∈ Set.Icc a b) :
-- imply
  x ∈ Set.Icc (a - 1) b := by
-- proof
  obtain ⟨hax, hxb⟩ := h
  exact ⟨by linarith, hxb⟩


-- created on 2023-08-20
