/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RoughNumbers.lean -/


import sympy.atlas.NumberTheory.RoughNumbers
import Lemma.Nat.RoughNumbers

/-!
# Examples for rough natural numbers

Focused checks of the source boundaries (`1`, primes, a composite rough number,
a rejected small-prime factor, zero), divisor closure, bound antitonicity, and
the smooth-number bridge.
-/


namespace Nat

-- The unit is rough at every bound.
example : (1 : ℕ).IsRough 10 :=
  isRough_one 10

-- A prime above the bound is rough.
example : (7 : ℕ).IsRough 5 :=
  (by decide : (7 : ℕ).Prime).isRough_iff.mpr (by decide)

-- A prime characterization check in both directions.
example : (5 : ℕ).IsRough 4 :=
  (by decide : (5 : ℕ).Prime).isRough_iff.mpr (by decide)

example : ¬ (5 : ℕ).IsRough 5 := by
  intro h
  have hlt := (by decide : (5 : ℕ).Prime).isRough_iff.mp h
  omega

-- A composite rough number: `35 = 5 * 7` has no prime factor `≤ 4`.
example : (35 : ℕ).IsRough 4 := by
  have h5 : (5 : ℕ).IsRough 4 :=
    (by decide : (5 : ℕ).Prime).isRough_iff.mpr (by decide)
  have h7 : (7 : ℕ).IsRough 4 :=
    (by decide : (7 : ℕ).Prime).isRough_iff.mpr (by decide)
  simpa using isRough_mul.mpr ⟨h5, h7⟩

-- Multiplication closure builds the composite from its prime factors.
example : (5 * 7 : ℕ).IsRough 4 :=
  isRough_mul.mpr
    ⟨(by decide : (5 : ℕ).Prime).isRough_iff.mpr (by decide),
      (by decide : (7 : ℕ).Prime).isRough_iff.mpr (by decide)⟩

-- A rejected small-prime factor: `2 ∣ 6` and `2 ≤ 2`.
example : ¬ (6 : ℕ).IsRough 2 := by
  intro h
  have hlt := h.lt_of_prime_dvd (by decide : (2 : ℕ).Prime) (by decide)
  omega

-- Zero is not rough.
example : ¬ (0 : ℕ).IsRough 5 :=
  fun h => h.ne_zero rfl

-- Positive divisors of a rough number are rough.
example : (7 : ℕ).IsRough 4 :=
  (isRough_mul.mpr
    ⟨(by decide : (5 : ℕ).Prime).isRough_iff.mpr (by decide),
      (by decide : (7 : ℕ).Prime).isRough_iff.mpr (by decide)⟩).of_dvd
    (dvd_mul_left 7 5) (by decide)

-- Antitonicity in the bound.
example : (35 : ℕ).IsRough 2 := by
  have h5 : (5 : ℕ).IsRough 4 :=
    (by decide : (5 : ℕ).Prime).isRough_iff.mpr (by decide)
  have h7 : (7 : ℕ).IsRough 4 :=
    (by decide : (7 : ℕ).Prime).isRough_iff.mpr (by decide)
  have h : (5 * 7 : ℕ).IsRough 2 :=
    isRough_mul.mpr ⟨h5.of_le (by decide), h7.of_le (by decide)⟩
  simpa using h

-- Smooth-number bridge: `1` is the only number both `5`-rough and `6`-smooth.
example : (1 : ℕ) = 1 :=
  (isRough_one 5).eq_one_of_mem_smoothNumbers
    ⟨one_ne_zero, fun _ hp => by simp at hp⟩

-- Nonunit source-rough numbers bounded by `N` land in `roughNumbersUpTo`.
example : (35 : ℕ) ∈ roughNumbersUpTo 100 5 := by
  have h5 : (5 : ℕ).IsRough 4 :=
    (by decide : (5 : ℕ).Prime).isRough_iff.mpr (by decide)
  have h7 : (7 : ℕ).IsRough 4 :=
    (by decide : (7 : ℕ).Prime).isRough_iff.mpr (by decide)
  have h : (5 * 7 : ℕ).IsRough 4 := isRough_mul.mpr ⟨h5, h7⟩
  have hm := h.mem_roughNumbersUpTo (N := 100) (by decide) (by decide)
  simpa using hm

end Nat
