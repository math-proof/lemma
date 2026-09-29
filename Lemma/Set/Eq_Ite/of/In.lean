import sympy.sets.sets
import sympy.Basic
open Classical


@[main]
private lemma expr_swap
  {x : ℤ}
  {S A : Set ℤ}
  {f g : ℤ → ℝ}
-- given
  (h : x ∈ S) :
-- imply
  (if x ∈ A ∩ S then f x else g x) = if x ∈ S \ (A ∩ S) then g x else f x := by
-- proof
  by_cases hA : x ∈ A
  · rw [if_pos ⟨hA, h⟩, if_neg (fun hx => hx.2 ⟨hA, h⟩)]
  · rw [if_neg (fun hx => hA hx.1), if_pos ⟨h, fun hx => hA hx.1⟩]


-- created on 2026-09-27
