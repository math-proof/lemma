import Mathlib.Data.Real.Sign
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  (fun i => Real.sign ((fun i => x i) i)) = fun i => Real.sign (x i) := by
-- proof
  rfl


-- created on 2023-05-24
