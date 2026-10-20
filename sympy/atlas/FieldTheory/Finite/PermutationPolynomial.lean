/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Permutation polynomials complete to level `k`

Source: S. Rajagopal and P. Vanchinathan, *Higher Level Completeness for
Permutation Polynomials* (arXiv `2310.12466v1`). A polynomial `f ∈ F_q[X]` is
complete to level `k` (`k`-complete) when `f` together with `f + x`, …,
`f + kx` are all permutation polynomials.
-/

namespace Polynomial

/-- A polynomial over a finite field is a permutation polynomial when its
evaluation self-map is bijective. -/
def IsPermutationPolynomial {F : Type*} [Field F] [Finite F]
    (f : Polynomial F) : Prop :=
  Function.Bijective fun x => f.eval x

/-- A polynomial `f` over a finite field is complete to level `k`
(`k`-complete) when `f + i * X` is a permutation polynomial for every natural
index `i ≤ k`, with `i` cast into `F`. The source assumes positive `k`; the
predicate is stated for all natural levels, with the positive-level
characterization `isKComplete_succ_iff` and the zero-level boundary
`isKComplete_zero` below. -/
def IsKComplete {F : Type*} [Field F] [Finite F] (f : Polynomial F)
    (k : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ k → IsPermutationPolynomial (f + Polynomial.C (i : F) * Polynomial.X)

/-- Unfolding characterization of level-`k` completeness. -/
theorem isKComplete_iff {F : Type*} [Field F] [Finite F] (f : Polynomial F)
    (k : ℕ) :
    IsKComplete f k ↔ ∀ i : ℕ, i ≤ k →
      Function.Bijective fun x =>
        (f + Polynomial.C (i : F) * Polynomial.X).eval x :=
  Iff.rfl

/-- Level-`k` completeness is downward monotone in the level. -/
theorem isKComplete_mono {F : Type*} [Field F] [Finite F] {f : Polynomial F}
    {j k : ℕ} (h : IsKComplete f k) (hle : j ≤ k) : IsKComplete f j :=
  fun i hi => h i (le_trans hi hle)

/-- Level zero is no extra condition: `0`-completeness is permutation. -/
theorem isKComplete_zero {F : Type*} [Field F] [Finite F] (f : Polynomial F) :
    IsKComplete f 0 ↔ IsPermutationPolynomial f := by
  constructor
  · intro h
    have h0 := h 0 le_rfl
    simpa using h0
  · intro h i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    simpa using h

/-- Source-facing positive-level characterization: `(k + 1)`-completeness splits
into `k`-completeness plus the new top translated polynomial. -/
theorem isKComplete_succ_iff {F : Type*} [Field F] [Finite F]
    (f : Polynomial F) (k : ℕ) :
    IsKComplete f (k + 1) ↔ IsKComplete f k ∧
      IsPermutationPolynomial
        (f + Polynomial.C ((k + 1 : ℕ) : F) * Polynomial.X) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (le_trans hi (Nat.le_succ k)), h (k + 1) le_rfl⟩
  · intro h i hi
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact h.2
    · exact h.1 i (Nat.le_of_lt_add_one hlt)

/-- The level condition includes index `0`, so a `k`-complete polynomial is
itself a permutation polynomial. -/
theorem isKComplete_self {F : Type*} [Field F] [Finite F] {f : Polynomial F}
    {k : ℕ} (h : IsKComplete f k) : IsPermutationPolynomial f := by
  have h0 := h 0 (Nat.zero_le k)
  simpa using h0

end Polynomial
