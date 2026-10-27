/-
Author: @akiezun, Avocado
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Def.Analysis.SpecialFunctions.Part1Ch5Entry10bEuleriansymmetry
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch5

namespace Entry10bEuleriansymmetry

open scoped BigOperators

open Finset

noncomputable section

/-- The initial even Euler number: `E_0 = 1`. -/
theorem chapter5EulerEven_zero : chapter5EulerEven 0 = 1 := by
  unfold chapter5EulerEven
  rw [Nat.strongRec_eq]
  simp

/-- Unfolding of `E_m` for `m ≠ 0` as a signed binomial sum over earlier values. -/
theorem chapter5EulerEven_step (m : ℕ) (hm : m ≠ 0) :
    chapter5EulerEven m =
      -∑ k : Fin m, (Nat.choose (2 * m) (2 * k.val) : ℤ) * chapter5EulerEven k.val := by
  conv_lhs => unfold chapter5EulerEven; rw [Nat.strongRec_eq]
  simp only [hm, ↓reduceIte]
  rfl

/-- The defining binomial recurrence for even Euler numbers:
`∑_{k = 0}^m (2m).choose (2k) * E_k` is `1` for `m = 0` and `0` otherwise. -/
theorem chapter5EulerEven_recurrence (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℤ) * chapter5EulerEven k =
      if m = 0 then 1 else 0 := by
  cases m with
  | zero => simp [chapter5EulerEven_zero]
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [Finset.sum_range_succ]
    have hlast : ((Nat.choose (2 * (m + 1)) (2 * (m + 1)) : ℕ) : ℤ) *
        chapter5EulerEven (m + 1) = chapter5EulerEven (m + 1) := by
      simp [Nat.choose_self]
    rw [hlast]
    have hstep := chapter5EulerEven_step (m + 1) (Nat.succ_ne_zero m)
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      ((Nat.choose (2 * (m+1)) (2 * k) : ℕ):ℤ) * chapter5EulerEven k)] at hstep
    linarith [hstep]

theorem eulerEven_recurrenceQ (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) * ((chapter5EulerEven k : ℤ) : ℚ) =
      if m = 0 then 1 else 0 := by
  have h := chapter5EulerEven_recurrence m
  have h2 : ((∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℤ) * chapter5EulerEven k : ℤ) : ℚ) =
      ((if m = 0 then (1 : ℤ) else 0 : ℤ) : ℚ) := by rw [h]
  rw [Int.cast_sum] at h2
  simp only [Int.cast_mul, Int.cast_natCast] at h2
  rw [h2]
  split <;> simp

theorem sum_range_two_mul_succ (g : ℕ → ℚ) (m : ℕ)
    (hg : ∀ k, Odd k → g k = 0) :
    ∑ k ∈ Finset.range (2 * m + 1), g k = ∑ j ∈ Finset.range (m + 1), g (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
    conv_lhs => rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, hg _ hodd, add_zero]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [ih]
    congr 1

end
end Entry10bEuleriansymmetry
end Ramanujan.Part1Ch5
end
