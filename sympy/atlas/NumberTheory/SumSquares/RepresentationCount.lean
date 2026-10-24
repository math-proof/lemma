/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Card

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval

/-!
# Ordered signed sums of squares
Ordered signed integer vectors and their representation numbers.
-/

namespace SumSquares

/-- Set of ordered signed integer vectors with squared norm `n`. -/
def solutions (k n : ℕ) : Set (Fin k → ℤ) :=
  { x | dotProduct x x = (n : ℤ) }

/-- Number of ordered signed representations of `n` as `k` squares. -/
noncomputable def representationNumber (k n : ℕ) : ℕ :=
  (solutions k n).ncard
end SumSquares
