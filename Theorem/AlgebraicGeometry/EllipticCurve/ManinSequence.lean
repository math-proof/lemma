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
