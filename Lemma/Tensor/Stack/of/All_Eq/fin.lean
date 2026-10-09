import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  (fun i : Fin n => f i) = (fun i : Fin n => g i) := by
-- proof
  funext i
  exact h i i.isLt


-- created on 2018-04-03
-- updated on 2021-12-31
