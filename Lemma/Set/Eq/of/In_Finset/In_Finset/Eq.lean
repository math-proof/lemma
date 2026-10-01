import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x y : ℝ}
  {f : ℝ → ℝ}
-- given
  (hx : x ∈ ({a, b} : Set ℝ))
  (hy : y ∈ ({a, b} : Set ℝ))
  (h : f a = f b) :
-- imply
  f x = f y := by
-- proof
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact h | exact h.symm


-- created on 2026-09-27
