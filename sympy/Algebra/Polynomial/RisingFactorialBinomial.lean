import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open scoped BigOperators

namespace MetaMathlibExt

/--
Binomial theorem for rising factorials: `(a + b)` raised to the rising
`n`-th power expands as the choose-weighted sum of products of the rising
powers of `a` and `b`.
-/
theorem ascPochhammer_eval_add (n : ℕ) (a b : ℝ) :
    (ascPochhammer ℝ n).eval (a + b) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        (ascPochhammer ℝ k).eval a *
        (ascPochhammer ℝ (n - k)).eval b := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    have hP : ∀ (m : ℕ) (x : ℝ),
        (ascPochhammer ℝ (m + 1)).eval x =
          (ascPochhammer ℝ m).eval x * (x + (m : ℝ)) :=
      fun m x => ascPochhammer_succ_eval m x
    rw [hP n (a + b), ih, Finset.sum_mul]
    have eAB : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n - k)).eval b * (a + b + (n : ℝ)))
        = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n + 1 - k)).eval b)
        + (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk_le : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      have hkn : ((n - k : ℕ) : ℝ) + (k : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hk_le
      have hPb : (ascPochhammer ℝ (n + 1 - k)).eval b
          = (ascPochhammer ℝ (n - k)).eval b * (b + ((n - k : ℕ) : ℝ)) := by
        have hsub : n + 1 - k = (n - k) + 1 := by omega
        rw [hsub]
        exact ascPochhammer_succ_eval (n - k) b
      have hPa : (ascPochhammer ℝ (k + 1)).eval a
          = (ascPochhammer ℝ k).eval a * (a + (k : ℝ)) :=
        ascPochhammer_succ_eval k a
      have hs : a + b + (n : ℝ)
          = (b + ((n - k : ℕ) : ℝ)) + (a + (k : ℝ)) := by
        rw [← hkn]; ring
      rw [hPb, hPa, hs]; ring
    rw [eAB]
    have e1 : (∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n + 1 - k)).eval b)
        = (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b)
        + ((n + 1).choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b :=
      Finset.sum_range_succ' _ _
    have eT : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b)
        = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b)
        + (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hC : (((n + 1).choose (k + 1) : ℕ) : ℝ)
          = (n.choose k : ℝ) + (n.choose (k + 1) : ℝ) := by
        rw [Nat.choose_succ_succ', Nat.cast_add]
      have hsub : n + 1 - (k + 1) = n - k := by omega
      rw [hsub, hC, add_mul, add_mul]
    have e3 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n + 1 - k)).eval b)
        = (∑ k ∈ Finset.range n, (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b)
        + (n.choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b :=
      Finset.sum_range_succ' _ _
    have eAsh : (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b)
        = (∑ k ∈ Finset.range n, (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b) + 0 := by
      have epeel : (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) *
            (ascPochhammer ℝ (k + 1)).eval a *
            (ascPochhammer ℝ (n - k)).eval b)
          = (∑ k ∈ Finset.range n, (n.choose (k + 1) : ℝ) *
            (ascPochhammer ℝ (k + 1)).eval a *
            (ascPochhammer ℝ (n - k)).eval b)
          + (n.choose (n + 1) : ℝ) *
            (ascPochhammer ℝ (n + 1)).eval a *
            (ascPochhammer ℝ (n - n)).eval b :=
        Finset.sum_range_succ _ _
      rw [epeel]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hsub : n + 1 - (k + 1) = n - k := by
          have := Finset.mem_range.mp hk
          omega
        rw [hsub]
      · have h0 : n.choose (n + 1) = 0 :=
          Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
        rw [h0]
        simp
    have hT0 : ((n + 1).choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b
        = (n.choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b := by
      simp
    rw [e1, eT, eAsh, hT0, e3, add_zero]
    ring

end MetaMathlibExt
