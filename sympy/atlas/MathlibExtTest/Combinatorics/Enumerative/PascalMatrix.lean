/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PascalMatrix.lean -/


import Mathlib.Tactic.NormNum
import sympy.atlas.Combinatorics.Enumerative.PascalMatrix
import Lemma.Finset.Enumerative.PascalMatrix

open scoped BigOperators Topology

namespace MetaMathlibExt

-- Concrete boundary calculations.
example : pascalEntry 4 2 = 6 := by rfl

example : pascalEntry 3 5 = 0 := by rfl

example : Finset.sum (Finset.range 4) (fun j => (pascalEntry 3 j : ℝ)) = 8 := by
  norm_num [pascalEntry, Finset.sum_range_succ, Nat.choose]

-- Generic API tests for all five public theorems.
example (x : ℝ) (hx : |x| < 1) : pascalAlpha 0 x = 1 / (1 - x) := by
  simpa using pascalAlpha_eq 0 x hx

example (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' j, pascalAlpha j x) = ∑' j, x ^ j / (1 - x) ^ (j + 1) :=
  (tsum_pascalAlpha_eq x hx).2

example (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' j, ∑' i, (pascalEntry i j : ℝ) * x ^ i) =
      (∑' i, ∑' j, (pascalEntry i j : ℝ) * x ^ i) :=
  (tsum_pascalEntry_comm x hx).1

example (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' i, x ^ i * Finset.sum (Finset.range (i + 1))
      (fun j => (pascalEntry i j : ℝ))) = 1 / (1 - 2 * x) :=
  tsum_pascalEntry_row x hx

example : (∑' i, ((2 : ℝ) * 0) ^ i) = 1 / (1 - 2 * (0 : ℝ)) := by
  have h := (tsum_pascalAlpha_eq_geometric (0 : ℝ) (by norm_num)).2
  simpa using h

example (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' j, pascalAlpha j x) = 1 / (1 - 2 * x) := by
  have h1 := (tsum_pascalAlpha_eq_geometric x hx).1
  have h2 := (tsum_pascalAlpha_eq_geometric x hx).2
  rw [h1, h2]

end MetaMathlibExt
