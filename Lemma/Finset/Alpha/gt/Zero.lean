import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range n).map x) > 0 := by
-- proof
  apply alpha_pos
  · simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  · intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact h i


-- created on 2020-09-17
