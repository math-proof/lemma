import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x y : α}
  {v : List.Vector α n} :
-- imply
  (x ::ᵥ v).push y = x ::ᵥ v.push y := by
-- proof
  induction n <;> rfl


-- created on 2024-12-22
