import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Def.AlgebraicGeometry.EllipticCurve.ManinSequence.Part2
/-!
# Integer sequences in Manin's proof

This file contains the elementary arithmetic at the end of Manin's proof of the Hasse bound.
-/


namespace AlgebraicGeometry.EllipticCurve

namespace ManinDegreeData

/-- Manin degree data implies the integral squared form of the Hasse bound. -/
theorem hasse_bound {q N : ℕ} (data : ManinDegreeData q N) :
    (((q : ℤ) + 1 - (N : ℤ)) ^ 2 ≤ 4 * (q : ℤ)) := by
  let dInt : ℤ → ℤ := fun n ↦ data.d n
  have hrec : ∀ n, dInt (n - 1) + dInt (n + 1) = 2 * dInt n + 2 := by
    intro n
    dsimp only [dInt]
    exact_mod_cast data.recurrence n
  have hzero : dInt 0 = q := by
    dsimp only [dInt]
    exact_mod_cast data.zero
  have hnegOne : dInt (-1) = N := by
    dsimp only [dInt]
    exact_mod_cast data.negOne
  have hquadratic (n : ℤ) :
      dInt n = n ^ 2 + ((q : ℤ) + 1 - (N : ℤ)) * n + q :=
    Int.eq_quadratic_of_recurrence dInt q N hrec hzero hnegOne n
  apply Int.sq_le_four_mul_of_quadratic_nonnegative
  · intro n
    rw [← hquadratic]
    exact Int.natCast_nonneg _
  · intro n hn hn1
    apply data.noAdjacentZeros n
    · apply Int.ofNat_injective
      simpa [dInt, hquadratic n] using hn
    · apply Int.ofNat_injective
      simpa [dInt, hquadratic (n + 1)] using hn1

end ManinDegreeData
end AlgebraicGeometry.EllipticCurve
