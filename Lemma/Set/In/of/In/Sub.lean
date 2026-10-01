import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b c : ℝ}
-- given
  (h : x - c ∈ Icc (a - c) (b - c)) :
-- imply
  x ∈ Icc a b := by
-- proof
  obtain ⟨h₀, h₁⟩ := h
  constructor <;> linarith


-- created on 2019-06-24
