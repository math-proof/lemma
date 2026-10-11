import sympy.sets.sets
import sympy.Basic
open Classical


@[path]
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
  · rw [ite_eq_left ⟨hA, h⟩, ite_eq_right (fun hx => hx.2 ⟨hA, h⟩)]
  · rw [ite_eq_right (fun hx => hA hx.1), ite_eq_left ⟨h, fun hx => hA hx.1⟩]


-- created on 2026-09-27
