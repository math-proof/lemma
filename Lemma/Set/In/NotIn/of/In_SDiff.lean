import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∈ A \ B) :
-- imply
  e ∈ A ∧ e ∉ B := by
-- proof
  -- Apply the definition of set difference to decompose the hypothesis h
  rw [Set.mem_diff] at h
  -- Since h now directly states e ∈ A ∧ e ∉ B, we can exact h to conclude the proof
  exact h


-- created on 2025-04-07
