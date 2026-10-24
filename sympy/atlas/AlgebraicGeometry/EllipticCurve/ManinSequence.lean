/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer sequences in Manin's proof

This file contains the elementary arithmetic at the end of Manin's proof of the Hasse bound.
-/

namespace Int
end Int
namespace MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The four properties of the polynomial-degree sequence used in Manin's proof. -/
structure ManinDegreeData (q N : ℕ) where
  /-- The numerator degree attached to the point indexed by an integer. -/
  d : ℤ → ℕ
  /-- Frobenius has degree `q`. -/
  zero : d 0 = q
  /-- Frobenius minus the identity has degree equal to the rational point count. -/
  negOne : d (-1) = N
  /-- The degree sequence has constant second difference two. -/
  recurrence : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2
  /-- Consecutive points in the sequence cannot both have degree zero. -/
  noAdjacentZeros : ∀ n, d n = 0 → d (n + 1) = 0 → False

namespace ManinDegreeData

/-- Build Manin degree data from its nonnegative quadratic formula, provided consecutive integer
values do not both vanish. -/
def ofQuadratic (q N : ℕ) (a : ℤ) (ha : a = (q : ℤ) + 1 - (N : ℤ))
    (hnonneg : ∀ n, 0 ≤ n ^ 2 + a * n + q)
    (hnoAdjacent : ∀ n, n ^ 2 + a * n + q = 0 →
      (n + 1) ^ 2 + a * (n + 1) + q = 0 → False) : ManinDegreeData q N where
  d n := (n ^ 2 + a * n + q).toNat
  zero := by simp
  negOne := by
    have h := hnonneg (-1)
    apply Int.ofNat_injective
    change (((-1 : ℤ) ^ 2 + a * (-1) + q).toNat : ℤ) = (N : ℤ)
    rw [Int.toNat_of_nonneg h]
    simp [ha]
    ring
  recurrence n := by
    have hm := hnonneg (n - 1)
    have hn := hnonneg n
    have hp := hnonneg (n + 1)
    apply Int.ofNat_injective
    change ((((n - 1) ^ 2 + a * (n - 1) + q).toNat : ℕ) : ℤ) +
        (((n + 1) ^ 2 + a * (n + 1) + q).toNat : ℕ) =
      2 * (((n ^ 2 + a * n + q).toNat : ℕ) : ℤ) + 2
    rw [Int.toNat_of_nonneg hm, Int.toNat_of_nonneg hn, Int.toNat_of_nonneg hp]
    ring
  noAdjacentZeros n hn hn1 := by
    apply hnoAdjacent n
    · exact le_antisymm (Int.toNat_eq_zero.mp hn) (hnonneg n)
    · exact le_antisymm (Int.toNat_eq_zero.mp hn1) (hnonneg (n + 1))
end ManinDegreeData
end MathlibExt.AlgebraicGeometry.EllipticCurve
