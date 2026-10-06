import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h : ∀ i < n, f i = 0) :
-- imply
  (fun i : Fin n => f i) = 0 := by
-- proof
  funext i
  exact h i i.isLt


-- created on 2022-01-01
