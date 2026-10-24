/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RisingDiagonalSequence.lean -/


import sympy.atlas.Combinatorics.Enumerative.RisingDiagonalSequence
import Lemma.Finset.Enumerative.RisingDiagonalSequence
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

/-- The constant unit triangle satisfies the binary binomial interpolated
triangle predicate with weights `α = β = 1 / 2`. -/
private def constTriangle : ℕ → ℕ → ℝ := fun _ _ => 1

/-- First rows of the `(a₀, a₁, α, β) = (0, 1, 1, 1)` triangle, whose column
zero is the Fibonacci sequence; off-table entries default to zero. -/
private def fibTriangleSample : ℕ → ℕ → ℝ
  | 0, 0 => 0
  | 1, 0 => 1
  | 1, 1 => 1
  | 2, 0 => 1
  | 2, 1 => 2
  | 2, 2 => 3
  | 3, 0 => 2
  | 3, 1 => 3
  | 3, 2 => 5
  | 3, 3 => 8
  | 4, 0 => 3
  | 4, 1 => 5
  | 4, 2 => 8
  | 4, 3 => 13
  | 4, 4 => 21
  | _, _ => 0

/-- The main theorem applies to any admissible triangle. -/
example {a : ℕ → ℕ → ℝ} {a₀ a₁ α β : ℝ}
    (h : IsBinaryBinomialInterpolatedTriangle a a₀ a₁ α β) (n : ℕ)
    (i j : Fin (n / 2 + 1)) :
    risingDiagonal a n i = risingDiagonal a n j :=
  risingDiagonal_const h n i j

/-- Rising diagonals of the constant triangle agree at concrete indices. -/
example : risingDiagonal constTriangle 4 ⟨1, by decide⟩ =
    risingDiagonal constTriangle 4 ⟨2, by decide⟩ :=
  risingDiagonal_const constTriangle_mem 4 _ _

/-- Level-two rising diagonal of the sample triangle: `a 2 0 = a 1 1 = 1`. -/
example : risingDiagonal fibTriangleSample 2 ⟨0, by decide⟩ = 1 := rfl

example : risingDiagonal fibTriangleSample 2 ⟨1, by decide⟩ = 1 := rfl

/-- Level-three rising diagonal of the sample triangle: `a 3 0 = a 2 1 = 2`. -/
example : risingDiagonal fibTriangleSample 3 ⟨0, by decide⟩ = 2 := rfl

example : risingDiagonal fibTriangleSample 3 ⟨1, by decide⟩ = 2 := rfl

/-- Level-four rising diagonal: `a 4 0 = a 3 1 = a 2 2 = 3`. -/
example : risingDiagonal fibTriangleSample 4 ⟨0, by decide⟩ = 3 := rfl

example : risingDiagonal fibTriangleSample 4 ⟨1, by decide⟩ = 3 := rfl

example : risingDiagonal fibTriangleSample 4 ⟨2, by decide⟩ = 3 := rfl

end MetaMathlibExt
