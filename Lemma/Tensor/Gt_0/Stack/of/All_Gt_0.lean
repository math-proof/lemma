import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h : ∀ i < n, f i > 0) :
-- imply
  ∀ i : Fin n, (fun i : Fin n => f i) i > 0 := by
-- proof
  exact fun i => h i i.isLt


-- created on 2022-01-01
