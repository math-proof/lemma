/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RisingDiagonalSequence.lean -/

module

public import Def.Combinatorics.Enumerative.RisingDiagonalSequence
public import Theorem.Finset.Enumerative.RisingDiagonalSequence
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MetaMathlibExt

/-- The constant unit triangle satisfies the binary binomial interpolated
triangle predicate with weights `α = β = 1 / 2`. -/
def constTriangle : ℕ → ℕ → ℝ := fun _ _ => 1

/-- First rows of the `(a₀, a₁, α, β) = (0, 1, 1, 1)` triangle, whose column
zero is the Fibonacci sequence; off-table entries default to zero. -/
def fibTriangleSample : ℕ → ℕ → ℝ
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

end MetaMathlibExt
