module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Monotone.booleanFourier.bool.false_true_of_le_ne
open BooleanFourier Bool


public section

/--
[chi_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {i : Fin n}
  {x : Fin n → Bool} :
-- imply
  chi {i} x = boolToReal (x i) := by
-- proof
  simp [chi]


theorem BooleanFourier.chi_singleton
  {n : ℕ}
  {i : Fin n}
  {x : Fin n → Bool} :
-- imply
  chi {i} x = boolToReal (x i) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
