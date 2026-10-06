import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {c n : ℕ}
  {f : ℕ → ℕ → ℝ} :
-- imply
  ∑ i : Fin c, (fun j : Fin n => f i j) = fun j : Fin n => ∑ i : Fin c, f i j := by
-- proof
  funext j
  simp


-- created on 2023-03-18
