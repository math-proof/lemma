/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

section

open scoped BigOperators

private def ff (n k : ℕ) : ℕ → ℕ := fun j =>
  ∑ i ∈ Finset.range (k + j + 1), Nat.choose (n + j - i) i

private lemma pascal_shift (N t : ℕ) :
    Nat.choose (N + 2 - (t + 1)) (t + 1) =
      Nat.choose (N + 1 - (t + 1)) (t + 1) + Nat.choose (N + 1 - (t + 1)) t := by
  by_cases h : t ≤ N
  · have e1 : N + 2 - (t + 1) = (N - t) + 1 := by omega
    have e2 : N + 1 - (t + 1) = N - t := by omega
    rw [e1, e2, Nat.choose_succ_succ']
    ac_rfl
  · have z1 : N + 2 - (t + 1) = 0 := by omega
    have z2 : N + 1 - (t + 1) = 0 := by omega
    rw [z1, z2]
    have h1 : (0 : ℕ) < t + 1 := by omega
    have h2 : (0 : ℕ) < t := by omega
    simp [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2]

private lemma eshift (N t : ℕ) :
    Nat.choose (N + 1 - (t + 1)) t = Nat.choose (N - t) t := by
  by_cases h : t ≤ N
  · have e : N + 1 - (t + 1) = N - t := by omega
    rw [e]
  · by_cases ht : t = 0
    · omega
    · have z1 : N + 1 - (t + 1) = 0 := by omega
      have z2 : N - t = 0 := by omega
      rw [z1, z2]

private lemma fib_step (N S : ℕ) :
    ∑ t ∈ Finset.range (S + 2), Nat.choose (N + 2 - t) t =
      (∑ t ∈ Finset.range (S + 1), Nat.choose (N - t) t) +
      (∑ t ∈ Finset.range (S + 2), Nat.choose (N + 1 - t) t) := by
  have c1 : S + 2 = (S + 1) + 1 := by omega
  rw [c1, Finset.sum_range_succ' (fun t => Nat.choose (N + 2 - t) t) (S + 1)]
  have c2 : S + 2 = (S + 1) + 1 := by omega
  rw [c2, Finset.sum_range_succ' (fun t => Nat.choose (N + 1 - t) t) (S + 1)]
  simp_rw [pascal_shift N, eshift N, Finset.sum_add_distrib]
  simp [Nat.choose_zero_right]
  omega

private lemma filip_aux : ∀ (h n k : ℕ),
    (∑ t ∈ Finset.range (k + h + 1), Nat.choose (n + 2 * h - t) t) =
    ∑ j ∈ Finset.range (h + 1), Nat.choose h j * ff n k j := by
  intro h
  refine Nat.rec (motive := fun h => ∀ (n k : ℕ),
    (∑ t ∈ Finset.range (k + h + 1), Nat.choose (n + 2 * h - t) t) =
    ∑ j ∈ Finset.range (h + 1), Nat.choose h j * ff n k j) ?_ ?_ h
  · intro n k
    simp [ff]
  · intro h ih n k
    have ih1 := ih n k
    have ih2 := ih (n + 1) (k + 1)
    have key := fib_step (n + 2 * h) (k + h)
    have eL : k + (h + 1) + 1 = (k + h) + 2 := by omega
    have eN : n + 2 * (h + 1) = (n + 2 * h) + 2 := by ring
    rw [eL, eN, key]
    rw [Finset.sum_range_succ' (fun j => Nat.choose (h + 1) j * ff n k j) (h + 1)]
    have hC0 : Nat.choose (h + 1) 0 = 1 := Nat.choose_zero_right _
    rw [hC0, one_mul]
    have hC : ∀ j : ℕ, Nat.choose (h + 1) (j + 1) =
        Nat.choose h j + Nat.choose h (j + 1) :=
      fun j => Nat.choose_succ_succ' h j
    simp_rw [hC, add_mul, Finset.sum_add_distrib]
    have hCh0 : Nat.choose h 0 = 1 := Nat.choose_zero_right h
    have hChh : Nat.choose h (h + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_succ_self h)
    have hR : (∑ j ∈ Finset.range (h + 1), Nat.choose h j * ff n k j) =
        ff n k 0 + (∑ j ∈ Finset.range (h + 1),
          Nat.choose h (j + 1) * ff n k (j + 1)) := by
      rw [Finset.sum_range_succ' (fun j => Nat.choose h j * ff n k j) h,
          Finset.sum_range_succ (fun j => Nat.choose h (j + 1) * ff n k (j + 1)) h,
          hCh0, hChh, one_mul, zero_mul, add_zero]
      ac_rfl
    have hFG : ∀ j : ℕ, ff n k (j + 1) =
        ∑ i ∈ Finset.range ((k + 1) + j + 1),
          Nat.choose ((n + 1) + j - i) i := by
      intro j
      have r1 : k + (j + 1) + 1 = (k + 1) + j + 1 := by omega
      have r2 : n + (j + 1) = (n + 1) + j := by omega
      simp only [ff, r1, r2]
    have b1 : (k + 1) + h + 1 = (k + h) + 2 := by omega
    have b2 : (n + 1) + 2 * h = ((n + 2 * h) + 1) := by ring
    rw [b1, b2] at ih2
    simp only [ff] at ih2
    simp_rw [← hFG] at ih2
    omega

/-- Filipponi binomial-sum formula for the incomplete Fibonacci triangle.

Hacène Belbachir and Amine Belkhir, "Combinatorial Expressions Involving Fibonacci,
Hyperfibonacci, and Incomplete Fibonacci Numbers", Journal of Integer Sequences 17 (2014),
Article 14.4.3. The formula is attributed there to P. Filipponi, "Incomplete Fibonacci and
Lucas numbers", Rend. Circ. Mat. Palermo 45 (1996), 37–56, DOI 10.1007/BF02845088.

Authoritative source: <https://cs.uwaterloo.ca/journals/JIS/VOL17/Belbachir/belb2.tex>.
Live/source file SHA-256
`e60c0875f28ac5be72af638a5a6d955c789993dfeed0f463afbb34955be8f2fe`.

Source definition of `f_r(s) = ∑_{j=0}^s choose(r-j,j)` at lines 304–319, and formula
`f_(n+2h)(k+h) = ∑_{j=0}^h choose(h,j) f_(n+j)(k+j)` at lines 347–371; extracted statement text
SHA-256 `c34b4ffa5811994595d796e20d6310141e9e6214ad20c93468c26bf2bc1233db`.

Stable task identifier `jis_grounded_1b088a32a9d82c1527d97e03__filipponi_binomial_sum_formula`.

All indices and inclusive bounds are preserved exactly: the defining sum runs `j = 0..s`
via `Finset.range (s + 1)`, and the outer sum runs `j = 0..h` via
`Finset.range (h + 1)`.

The truncated-subtraction identity holds unconditionally: out-of-range binomial
terms vanish, so no range hypotheses are needed.
-/
theorem filipponi_binomial_sum_formula_general
    (n h k : ℕ) :
    let f : ℕ → ℕ → ℕ := fun r s =>
      ∑ j ∈ Finset.range (s + 1), Nat.choose (r - j) j
    f (n + 2 * h) (k + h) =
      ∑ j ∈ Finset.range (h + 1), Nat.choose h j * f (n + j) (k + j) := by
  have hbase := filip_aux h n k
  change (∑ t ∈ Finset.range (k + h + 1), Nat.choose (n + 2 * h - t) t) =
    ∑ j ∈ Finset.range (h + 1), Nat.choose h j *
      (∑ i ∈ Finset.range (k + j + 1), Nat.choose (n + j - i) i)
  exact hbase

set_option linter.unusedVariables false in
/-- Source-faithful corollary of `filipponi_binomial_sum_formula_general` retaining
the displayed source condition `0 ≤ k ≤ (n-h)/2`, encoded as `h ≤ n` and
`2 * k ≤ n - h`. The hypotheses are unused since the truncated-subtraction
identity holds unconditionally.

Proves `Wanted` entry `filipponi_binomial_sum_formula`.
-/
theorem filipponi_binomial_sum_formula
    (n h k : ℕ) (hhn : h ≤ n) (hk : 2 * k ≤ n - h) :
    let f : ℕ → ℕ → ℕ := fun r s =>
      ∑ j ∈ Finset.range (s + 1), Nat.choose (r - j) j
    f (n + 2 * h) (k + h) =
      ∑ j ∈ Finset.range (h + 1), Nat.choose h j * f (n + j) (k + j) :=
  filipponi_binomial_sum_formula_general n h k

end

end MetaMathlibExt
