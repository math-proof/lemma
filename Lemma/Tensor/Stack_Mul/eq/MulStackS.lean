import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {a b : ℕ → ℝ} :
-- imply
  (fun i : Fin n => a i * b i) = (fun i : Fin n => a i) * (fun i : Fin n => b i) := by
-- proof
  funext i
  rfl


-- created on 2022-06-07
-- updated on 2023-06-08
