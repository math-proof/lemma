import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → Fin n → ℝ} :
-- imply
  (fun i : Fin n => ∑ j : Fin n, x j i) = ∑ j : Fin n, (fun i : Fin n => x j i) := by
-- proof
  funext i
  simp


-- created on 2019-10-21
