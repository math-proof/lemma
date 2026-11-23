/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SumSquares/RepresentationCount.lean -/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.NormNum
public import Def.NumberTheory.SumSquares.RepresentationCount
public import Theorem.Nat.SumSquares.RepresentationCount
open SumSquares

/-!
# Tests for ordered signed sums of squares
-/

public section


example : (![3, 4] : Fin 2 → ℤ) ∈ solutions 2 25 := by
  norm_num [mem_solutions, dotProduct, Fin.sum_univ_two]

example : (![-3, 4] : Fin 2 → ℤ) ∈ solutions 2 25 := by
  norm_num [mem_solutions, dotProduct, Fin.sum_univ_two]

example : (![4, 3] : Fin 2 → ℤ) ∈ solutions 2 25 := by
  norm_num [mem_solutions, dotProduct, Fin.sum_univ_two]

example : (![3, 3] : Fin 2 → ℤ) ∉ solutions 2 25 := by
  norm_num [mem_solutions, dotProduct, Fin.sum_univ_two]

example : (![3, 4] : Fin 2 → ℤ) ≠ (![-3, 4] : Fin 2 → ℤ) := by
  decide

example : (![3, 4] : Fin 2 → ℤ) ≠ (![4, 3] : Fin 2 → ℤ) := by
  decide

example (k n : ℕ) : Set.Finite (solutions k n) :=
  solutions_finite k n

example (k n : ℕ) :
    representationNumber k n = (solutions_finite k n).toFinset.card :=
  representationNumber_eq_toFinset_card k n

example : representationNumber 0 0 = 1 :=
  representationNumber_zero_zero

example (n : ℕ) : representationNumber 0 (n + 1) = 0 :=
  representationNumber_zero_succ n

example : representationNumber 1 0 = 1 :=
  representationNumber_one_zero

