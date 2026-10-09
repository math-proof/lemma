import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f g : ℝ → ℝ}
-- given
  (h : ∀ x ∈ S, f x = g x) :
-- imply
  ArgMax S f = ArgMax S g := by
-- proof
  unfold ArgMax
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [← h y hy', ← h x hx]; exact hy y hy'⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [h y hy', h x hx]; exact hy y hy'⟩


-- created on 2019-01-07
-- updated on 2023-05-04
