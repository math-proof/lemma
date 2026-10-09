import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer sequences in Manin's proof

This file contains the elementary arithmetic at the end of Manin's proof of the Hasse bound.
-/

namespace Int

/-- A two-sided integer sequence with constant second difference two is the expected monic
quadratic once its values at `0` and `-1` are known. -/
theorem eq_quadratic_of_recurrence (d : ℤ → ℤ) (q N : ℤ)
    (hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2)
    (hzero : d 0 = q) (hnegOne : d (-1) = N) (n : ℤ) :
    d n = n ^ 2 + (q + 1 - N) * n + q := by
  let p : ℤ → ℤ := fun m ↦ m ^ 2 + (q + 1 - N) * m + q
  have hp (m : ℤ) : p (m - 1) + p (m + 1) = 2 * p m + 2 := by
    simp only [p]
    ring
  have hpzero : p 0 = q := by
    simp [p]
  have hpnegOne : p (-1) = N := by
    simp [p]
    ring
  have hpair : ∀ m : ℤ, d m = p m ∧ d (m - 1) = p (m - 1) := by
    intro m
    refine Int.inductionOn' m 0 ?_ ?_ ?_
    · exact ⟨hzero.trans hpzero.symm, by simpa using hnegOne.trans hpnegOne.symm⟩
    · intro k _ hk
      refine ⟨?_, ?_⟩
      · linarith [hrec k, hp k]
      · simpa only [add_sub_cancel_right] using hk.1
    · intro k _ hk
      refine ⟨hk.2, ?_⟩
      have hd := hrec (k - 1)
      have hpd := hp (k - 1)
      rw [show k - 1 + 1 = k by ring] at hd hpd
      linarith
  exact (hpair n).1

/-- An integral monic quadratic that is nonnegative at every integer and does not vanish at two
consecutive integers has nonpositive discriminant. -/
theorem sq_le_four_mul_of_quadratic_nonnegative {a q : ℤ}
    (hnonneg : ∀ n : ℤ, 0 ≤ n ^ 2 + a * n + q)
    (hnotTwoZeros : ∀ n : ℤ,
      n ^ 2 + a * n + q = 0 → (n + 1) ^ 2 + a * (n + 1) + q = 0 → False) :
    a ^ 2 ≤ 4 * q := by
  by_contra hle
  have hbad : 4 * q < a ^ 2 := lt_of_not_ge hle
  rcases Int.even_or_odd a with ha | ha
  · obtain ⟨k, hk⟩ := ha
    have h := hnonneg (-k)
    rw [hk] at hbad h
    nlinarith
  · obtain ⟨k, hk⟩ := ha
    have hleft := hnonneg (-k - 1)
    have hright := hnonneg (-k)
    have hzleft : (-k - 1) ^ 2 + a * (-k - 1) + q = 0 := by
      rw [hk] at hbad hleft hright ⊢
      nlinarith
    have hzright : (-k) ^ 2 + a * (-k) + q = 0 := by
      rw [hk] at hbad hleft hright ⊢
      nlinarith
    apply hnotTwoZeros (-k - 1) hzleft
    convert hzright using 1
    ring

end Int

namespace AlgebraicGeometry.EllipticCurve

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
