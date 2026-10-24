/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ZagierMatrixInverse.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic

open scoped BigOperators

section

namespace MetaMathlibExt

/-- Zagier's `(K - 1) × (K - 1)` rational matrix, with source indices shifted from
`1, ..., K - 1` to `Fin (K - 1)`. -/
def zagierMatrix (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := fun i j =>
  (Nat.choose (2 * K - 2 * (j.val + 1)) (2 * (i.val + 1) - 1) : ℚ)
    + (Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1)) : ℚ)

/-- The first Bernoulli-number formula for the inverse of `zagierMatrix`. -/
def zagierInverseP (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := fun i j =>
  (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1)
    * ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
      (Nat.choose (2 * (j.val + 1) - 1) (2 * K - 2 * (i.val + 1) - n + 1) : ℚ)
        * (Nat.choose (n + 2 * (i.val + 1) - 2) n : ℚ) * bernoulli n

/-- The second Bernoulli-number formula for the inverse of `zagierMatrix`. -/
def zagierInverseQ (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := fun i j =>
  (-2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1)
    * ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
      (Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1) - n + 1) : ℚ)
        * (Nat.choose (n + 2 * (i.val + 1) - 2) n : ℚ) * bernoulli n
end MetaMathlibExt
end
