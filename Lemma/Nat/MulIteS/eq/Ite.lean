import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : α}
  {A B : Set α}
  [DecidablePred (· ∈ A)]
  [DecidablePred (· ∈ B)]
  {f g h p : α → ℝ} :
-- imply
  (if x ∈ A then f x else g x) * (if x ∈ B then h x else p x) =
      if x ∈ A ∧ x ∈ B then f x * h x else if x ∈ A then f x * p x else if x ∈ B then g x * h x else g x * p x := by
-- proof
  by_cases ha : x ∈ A
  · by_cases hb : x ∈ B
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : x ∈ B
    · simp [ha, hb]
    · simp [ha, hb]


-- created on 2026-09-27
