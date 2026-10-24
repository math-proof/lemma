import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[gib_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MelhamGibonacci.lean)
-/
@[path]
private lemma gib_shift (G : ℤ → ℤ)
  (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (i : ℤ) (m : ℕ) :
  G (i + (m : ℤ) + 1) =
    ((Nat.fib (m + 1) : ℕ) : ℤ) * G (i + 1) +
      ((Nat.fib m : ℕ) : ℤ) * G i := by
  have both : ∀ t : ℕ, G (i + (t : ℤ) + 1) =
    ((Nat.fib (t + 1) : ℕ) : ℤ) * G (i + 1) +
      ((Nat.fib t : ℕ) : ℤ) * G i ∧
    G (i + ((t + 1 : ℕ) : ℤ) + 1) =
      ((Nat.fib (t + 1 + 1) : ℕ) : ℤ) * G (i + 1) +
        ((Nat.fib (t + 1) : ℕ) : ℤ) * G i := by
    intro t
    induction t with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [Nat.fib_one, Nat.fib_zero]
      · have h := hG i
        have eL : i + (((0 + 1 : ℕ)) : ℤ) + 1 = i + 2 := by push_cast; ring
        have e1 : (0 + 1 + 1 : ℕ) = 2 := by ring
        have e2 : (0 + 1 : ℕ) = 1 := by ring
        rwa [eL, e1, e2, Nat.fib_two, Nat.fib_one, Nat.cast_one, one_mul, one_mul]
    | succ n ih =>
      obtain ⟨hPn, hPn1⟩ := ih
      refine ⟨hPn1, ?_⟩
      have hrec := hG (i + (n : ℤ) + 1)
      have eL : (i + (n : ℤ) + 1) + 2 = i + (((n + 1 + 1 : ℕ)) : ℤ) + 1 := by
        push_cast; ring
      have eM : (i + (n : ℤ) + 1) + 1 = i + (((n + 1 : ℕ)) : ℤ) + 1 := by
        push_cast; ring
      rw [eL, eM] at hrec
      rw [hPn1, hPn] at hrec
      have fA0 := Nat.fib_add_two (n := n + 1)
      have en : n + 1 + 2 = n + 1 + 1 + 1 := by ring
      rw [en] at fA0
      have fB0 := Nat.fib_add_two (n := n)
      have en2 : n + 2 = n + 1 + 1 := by ring
      rw [en2] at fB0
      have fAz : ((Nat.fib (n + 1 + 1 + 1) : ℕ) : ℤ) =
        ((Nat.fib (n + 1) : ℕ) : ℤ) + ((Nat.fib (n + 1 + 1) : ℕ) : ℤ) := by
        exact_mod_cast fA0
      have fBz : ((Nat.fib (n + 1 + 1) : ℕ) : ℤ) =
        ((Nat.fib n : ℕ) : ℤ) + ((Nat.fib (n + 1) : ℕ) : ℤ) := by
        exact_mod_cast fB0
      rw [hrec]
      linear_combination -(G (i + 1)) * fAz - (G i) * fBz
  exact (both m).1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[gib_sum_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MelhamGibonacci.lean)
-/
@[path]
private lemma gib_sum_sq (G : ℤ → ℤ)
  (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k : ℤ) (n : ℕ) :
  ∑ j ∈ Finset.range (2 * n), (G (k + j)) ^ 2 =
    ((Nat.fib (2 * n) : ℕ) : ℤ) *
      ((G (k + (n : ℤ) - 1)) ^ 2 + (G (k + (n : ℤ))) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : G (k + (n : ℤ) + 1) = G (k + (n : ℤ)) + G (k + (n : ℤ) - 1) := by
      have h := hG (k + (n : ℤ) - 1)
      have e1 : (k + (n : ℤ) - 1) + 2 = k + (n : ℤ) + 1 := by ring
      have e2 : (k + (n : ℤ) - 1) + 1 = k + (n : ℤ) := by ring
      rwa [e1, e2] at h
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have s1 := gib_shift G hG (k + (n : ℤ) - 1) n
    have q1 : (k + (n : ℤ) - 1) + (n : ℤ) + 1 = k + (((2 * n : ℕ)) : ℤ) := by
      push_cast; ring
    have q2 : (k + (n : ℤ) - 1) + 1 = k + (n : ℤ) := by ring
    rw [q1, q2] at s1
    have s2 := gib_shift G hG (k + (n : ℤ) - 1) (n + 1)
    have q3 : (k + (n : ℤ) - 1) + (((n + 1 : ℕ)) : ℤ) + 1 =
      k + (((2 * n + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [q3, q2] at s2
    rw [s1, s2]
    have kr1 : k + (((n + 1 : ℕ)) : ℤ) - 1 = k + (n : ℤ) := by push_cast; ring
    have kr2 : k + (((n + 1 : ℕ)) : ℤ) = k + (n : ℤ) + 1 := by push_cast; ring
    have kF : 2 * n + 1 + 1 = 2 * n + 2 := by ring
    rw [kr1, kr2, kF, hc]
    have d10 := Nat.fib_add n n
    have ed1 : n + n + 1 = 2 * n + 1 := by ring
    rw [ed1] at d10
    have d1 : ((Nat.fib (2 * n + 1) : ℕ) : ℤ) =
      ((Nat.fib n : ℕ) : ℤ) * ((Nat.fib n : ℕ) : ℤ) +
        ((Nat.fib (n + 1) : ℕ) : ℤ) * ((Nat.fib (n + 1) : ℕ) : ℤ) := by
      exact_mod_cast d10
    have d20 := Nat.fib_add (n + 1) n
    have ed2 : (n + 1) + n + 1 = 2 * n + 2 := by ring
    rw [ed2] at d20
    have d2 : ((Nat.fib (2 * n + 2) : ℕ) : ℤ) =
      ((Nat.fib (n + 1) : ℕ) : ℤ) * ((Nat.fib n : ℕ) : ℤ) +
        ((Nat.fib (n + 1 + 1) : ℕ) : ℤ) * ((Nat.fib (n + 1) : ℕ) : ℤ) := by
      exact_mod_cast d20
    have d30 := Nat.fib_add (n + 1) (n + 1)
    have ed3 : (n + 1) + (n + 1) + 1 = 2 * n + 3 := by ring
    rw [ed3] at d30
    have d3 : ((Nat.fib (2 * n + 3) : ℕ) : ℤ) =
      ((Nat.fib (n + 1) : ℕ) : ℤ) * ((Nat.fib (n + 1) : ℕ) : ℤ) +
        ((Nat.fib (n + 1 + 1) : ℕ) : ℤ) *
          ((Nat.fib (n + 1 + 1) : ℕ) : ℤ) := by
      exact_mod_cast d30
    have r10 := Nat.fib_add_two (n := 2 * n)
    have r1 : ((Nat.fib (2 * n) : ℕ) : ℤ) + ((Nat.fib (2 * n + 1) : ℕ) : ℤ) =
      ((Nat.fib (2 * n + 2) : ℕ) : ℤ) := by
      exact_mod_cast r10.symm
    have r20 := Nat.fib_add_two (n := 2 * n + 1)
    have ea : (2 * n + 1) + 2 = 2 * n + 3 := by ring
    have eb : (2 * n + 1) + 1 = 2 * n + 2 := by ring
    rw [ea, eb] at r20
    have r2 : ((Nat.fib (2 * n + 3) : ℕ) : ℤ) =
      ((Nat.fib (2 * n + 1) : ℕ) : ℤ) +
      ((Nat.fib (2 * n + 2) : ℕ) : ℤ) := by
      exact_mod_cast r20
    linear_combination (G (k + (n : ℤ) - 1)) ^ 2 * r1 -
      (G (k + (n : ℤ) - 1)) ^ 2 * d1 -
      2 * (G (k + (n : ℤ) - 1)) * (G (k + (n : ℤ))) * d2 +
      (G (k + (n : ℤ))) ^ 2 * r1 + (G (k + (n : ℤ))) ^ 2 * r2 -
      (G (k + (n : ℤ))) ^ 2 * d3

end MetaMathlibExt

namespace MetaMathlibExt

/--
[melham_fibonacci_gibonacci_sum_of_squares_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MelhamGibonacci.lean)
-/
@[path]
lemma melham_fibonacci_gibonacci_sum_of_squares_general
  {G : ℤ → ℤ}
  {k : ℤ}
  {n : ℕ}
-- given
  (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
-- imply
  6 * (∑ j ∈ Finset.range (2 * n), (G (k + j)) ^ 2) ^ 2 =
    (Nat.fib (2 * n) : ℤ) ^ 2 *
    ((G (k + n - 2)) ^ 4 + 4 * (G (k + n - 1)) ^ 4 +
    4 * (G (k + n)) ^ 4 + (G (k + n + 1)) ^ 4) := by
-- proof
  have key := gib_sum_sq G hG k n
  have hw : G (k + (n : ℤ)) = G (k + (n : ℤ) - 1) + G (k + (n : ℤ) - 2) := by
    have h := hG (k + (n : ℤ) - 2)
    have e1 : (k + (n : ℤ) - 2) + 2 = k + (n : ℤ) := by ring
    have e2 : (k + (n : ℤ) - 2) + 1 = k + (n : ℤ) - 1 := by ring
    rwa [e1, e2] at h
  have hz : G (k + (n : ℤ) + 1) = G (k + (n : ℤ)) + G (k + (n : ℤ) - 1) := by
    have h := hG (k + (n : ℤ) - 1)
    have e1 : (k + (n : ℤ) - 1) + 2 = k + (n : ℤ) + 1 := by ring
    have e2 : (k + (n : ℤ) - 1) + 1 = k + (n : ℤ) := by ring
    rwa [e1, e2] at h
  have w_eq : G (k + (n : ℤ) - 2) = G (k + (n : ℤ)) - G (k + (n : ℤ) - 1) := by
    rw [hw]; ring
  have quart : (G (k + (n : ℤ) - 2)) ^ 4 + 4 * (G (k + (n : ℤ) - 1)) ^ 4 +
    4 * (G (k + (n : ℤ))) ^ 4 + (G (k + (n : ℤ) + 1)) ^ 4 =
    6 * ((G (k + (n : ℤ) - 1)) ^ 2 + (G (k + (n : ℤ))) ^ 2) ^ 2 := by
    rw [w_eq, hz]; ring
  rw [key, quart]
  ring
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[melham_fibonacci_gibonacci_sum_of_squares](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MelhamGibonacci.lean)
-/
@[path]
lemma melham_fibonacci_gibonacci_sum_of_squares
  {G : ℤ → ℤ}
  {k : ℤ}
  {n : ℕ}
-- given
  (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
  (hG_nonzero : G 0 ≠ 0 ∨ G 1 ≠ 0)
  (hn : 0 < n) :
-- imply
  6 * (∑ j ∈ Finset.range (2 * n), (G (k + j)) ^ 2) ^ 2 =
    (Nat.fib (2 * n) : ℤ) ^ 2 *
    ((G (k + n - 2)) ^ 4 + 4 * (G (k + n - 1)) ^ 4 +
    4 * (G (k + n)) ^ 4 + (G (k + n + 1)) ^ 4) :=
-- proof
  melham_fibonacci_gibonacci_sum_of_squares_general G hG k n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
