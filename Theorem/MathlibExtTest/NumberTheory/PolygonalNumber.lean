/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PolygonalNumber.lean -/

import Theorem.NumberTheory.PolygonalNumber
import Lemma.Nat.PolygonalNumber


namespace Nat

-- Exact values by computation.
example : polygonalNumber 3 4 = 10 := by decide

example : polygonalNumber 4 5 = 25 := by decide

example : polygonalNumber 5 4 = 22 := by decide

example : polygonalNumber 6 4 = 28 := by decide

example : polygonalNumber 7 2 = 7 := by decide

example : polygonalNumber 5 3 = 12 := by decide

-- Totalization at `s < 3`: truncated subtraction gives `s - 2 = 0`, so the value is `n`.
example : polygonalNumber 0 4 = 4 := by decide

example : polygonalNumber 1 4 = 4 := by decide

example : polygonalNumber 2 4 = 4 := by decide

-- Simplification and initial-value API, including source-domain boundaries.
example (s : ℕ) : polygonalNumber s 0 = 0 := polygonalNumber_zero s

example (s : ℕ) : polygonalNumber s 1 = 1 := polygonalNumber_one s

example (s : ℕ) (hs : 3 ≤ s) : polygonalNumber s 2 = s := polygonalNumber_at_two s hs

example (s : ℕ) (hs : 3 ≤ s) : polygonalNumber s 3 = 3 * s - 3 :=
  polygonalNumber_at_three s hs

example (s : ℕ) (hs : 3 ≤ s) : polygonalNumber s 4 = 6 * s - 8 :=
  polygonalNumber_at_four s hs

-- Specialization API.
example (n : ℕ) : polygonalNumber 3 n = n * (n + 1) / 2 := polygonalNumber_three n

example (n : ℕ) : polygonalNumber 4 n = n ^ 2 := polygonalNumber_four n

example (n : ℕ) : polygonalNumber 5 n = (3 * n ^ 2 - n) / 2 := polygonalNumber_five n

example (n : ℕ) : polygonalNumber 6 n = 2 * n ^ 2 - n := polygonalNumber_six n

end Nat
