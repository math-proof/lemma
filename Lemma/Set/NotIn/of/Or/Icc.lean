import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h : x = b ∨ x ∉ Set.Icc a b) :
-- imply
  x ∉ Set.Ico a b := by
-- proof
  rcases h with h | h
  · rw [h]
    simp
  · intro hx
    exact h ⟨hx.1, hx.2.le⟩


-- created on 2020-10-20
