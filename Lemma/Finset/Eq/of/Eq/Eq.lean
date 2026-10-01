import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma catalan.recurrence
  {C : ℕ → ℤ}
  {n : ℕ}
-- given
  (h₀ : C 0 = 1)
  (h₁ : ∀ n, C (n + 1) = ∑ k ∈ Finset.range (n + 1), C k * C (n - k)) :
-- imply
  (C n : ℚ) = ((n * 2).choose n : ℚ) / (n + 1) := by
-- proof
  have hc : ∀ m, C m = catalan m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      cases m with
      | zero => rw [h₀, catalan_zero]; rfl
      | succ k =>
        rw [h₁, catalan_succ, ← Finset.sum_range (fun i => catalan i * catalan (k - i))]
        push_cast
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [ih i (by omega), ih (k - i) (by omega)]
  rw [hc, eq_div_iff (by positivity)]
  have h := congrArg (Nat.cast : ℕ → ℚ) (succ_mul_catalan_eq_centralBinom n)
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  push_cast at h
  rw [show n * 2 = 2 * n by ring]
  push_cast
  linarith


@[main]
private lemma permutation.push
  {n : ℕ}
  {p : ℕ → ℕ}
-- given
  (h₀ : (Finset.range n).biUnion (fun k => {p k}) = Finset.range n)
  (h₁ : p n = n) :
-- imply
  (Finset.range (n + 1)).biUnion (fun k => {p k}) = Finset.range (n + 1) := by
-- proof
  rw [Finset.range_add_one, Finset.biUnion_insert, h₀, h₁, Finset.insert_eq]


-- created on 2026-09-27
