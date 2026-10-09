import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma pigeonhole
  {k n : ℕ}
  {x : ℕ → ℕ}
-- given
  (hk : k > 0)
  (_hn : n > 0)
  (h : ∑ i ∈ Finset.range k, x i = n) :
-- imply
  ∃ i < k, (x i : ℤ) ≥ ⌈(n : ℝ) / k⌉ := by
-- proof
  by_contra hc
  simp only [not_exists, not_and, not_le] at hc
  have hlt : ∀ i ∈ Finset.range k, (x i : ℝ) < (n : ℝ) / k := fun i hi => by
    have := hc i (Finset.mem_range.mp hi)
    rw [Int.lt_ceil] at this
    exact_mod_cast this
  have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) hlt
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e : (k : ℝ) * ((n : ℝ) / k) = n := by field_simp
  have hs : (∑ i ∈ Finset.range k, (x i : ℝ)) = n := by exact_mod_cast h
  linarith


-- created on 2022-07-06
