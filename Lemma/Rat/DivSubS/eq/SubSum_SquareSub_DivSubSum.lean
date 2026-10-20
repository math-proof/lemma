import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {n t : ℕ}
  {x : ℕ → ℚ}
-- given
  (h₀ : 2 ≤ n)
  (h₁ : t < n) :
-- imply
  ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i - x j) ^ 2) -
      ∑ i ∈ Finset.range n, (x i - x t) ^ 2) / (n - 1 : ℚ) =
    ∑ i ∈ Finset.range n,
        (x i - ((∑ k ∈ Finset.range n, x k) - x t) / (n - 1 : ℚ)) ^ 2 -
      (x t - ((∑ k ∈ Finset.range n, x k) - x t) / (n - 1 : ℚ)) ^ 2 := by
-- proof
  set S : ℚ := ∑ k ∈ Finset.range n, x k
  set Q : ℚ := ∑ k ∈ Finset.range n, x k ^ 2
  have hcast : (↑(n - 1) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hsq : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i - x j) ^ 2 =
    (n : ℚ) * Q - S ^ 2 := by
    have hstep : ∀ m : ℕ, ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i, (x i - x j) ^ 2 =
      (m : ℚ) * ∑ i ∈ Finset.range m, x i ^ 2 - (∑ i ∈ Finset.range m, x i) ^ 2 := by
      intro m
      induction m with
      | zero =>
        simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => x i ^ 2),
          Finset.sum_range_succ (fun i => x i), ih, Nat.cast_succ]
        have hrow : ∑ j ∈ Finset.range m, (x m - x j) ^ 2 =
          (m : ℚ) * x m ^ 2 - 2 * x m * ∑ j ∈ Finset.range m, x j +
          ∑ j ∈ Finset.range m, x j ^ 2 := by
          trans ∑ j ∈ Finset.range m, (x m ^ 2 - 2 * x m * x j + x j ^ 2)
          ·
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ← Finset.mul_sum]
        rw [hrow]
        ring
    simpa [S, Q] using hstep n
  have hdev : ∑ i ∈ Finset.range n, (x i - x t) ^ 2 =
    Q - 2 * x t * S + (n : ℚ) * x t ^ 2 := by
    trans ∑ i ∈ Finset.range n, (x i ^ 2 - 2 * x t * x i + x t ^ 2)
    ·
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
  have hnz : (n : ℚ) - 1 ≠ 0 := by
    rw [← hcast]
    exact_mod_cast show n - 1 ≠ 0 by omega
  have hnum : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i - x j) ^ 2) -
    ∑ i ∈ Finset.range n, (x i - x t) ^ 2 =
    ((n : ℚ) - 1) * (Q - x t ^ 2) - (S - x t) ^ 2 := by
    rw [hsq, hdev]
    ring
  set μ : ℚ := (S - x t) / ((n : ℚ) - 1)
  have ht : t ∈ Finset.range n := Finset.mem_range.mpr h₁
  have hrest : ∑ i ∈ Finset.range n, (x i - μ) ^ 2 - (x t - μ) ^ 2 =
    ∑ i ∈ (Finset.range n).erase t, (x i - μ) ^ 2 := by
    rw [← Finset.add_sum_erase (s := Finset.range n) (f := fun i => (x i - μ) ^ 2) ht]
    ring
  have hx : ∑ i ∈ (Finset.range n).erase t, x i = S - x t := by
    have h := Finset.add_sum_erase (s := Finset.range n) (f := x) ht
    unfold S at *
    linear_combination h
  have hx2 : ∑ i ∈ (Finset.range n).erase t, x i ^ 2 = Q - x t ^ 2 := by
    have h := Finset.add_sum_erase (s := Finset.range n) (f := fun i => x i ^ 2) ht
    unfold Q at *
    linear_combination h
  have hcard : ((Finset.range n).erase t).card = n - 1 := by
    rw [Finset.card_erase_of_mem ht, Finset.card_range]
  have hsse : ∑ i ∈ (Finset.range n).erase t, (x i - μ) ^ 2 =
    Q - x t ^ 2 - (S - x t) ^ 2 / ((n : ℚ) - 1) := by
    trans ∑ i ∈ (Finset.range n).erase t, (x i ^ 2 - 2 * μ * x i + μ ^ 2)
    ·
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul,
      ← Finset.mul_sum, hx, hx2, hcast]
    unfold μ
    field_simp [hnz]
    ring
  calc
    _ = (((n : ℚ) - 1) * (Q - x t ^ 2) - (S - x t) ^ 2) / ((n : ℚ) - 1) := by
      rw [hnum]
    _ = Q - x t ^ 2 - (S - x t) ^ 2 / ((n : ℚ) - 1) := by
      field_simp [hnz]
    _ = ∑ i ∈ (Finset.range n).erase t, (x i - μ) ^ 2 := by
      rw [hsse]
    _ = ∑ i ∈ Finset.range n, (x i - μ) ^ 2 - (x t - μ) ^ 2 := by
      rw [hrest]
    _ = ∑ i ∈ Finset.range n, (x i - ((∑ k ∈ Finset.range n, x k) - x t) / (n - 1 : ℚ)) ^ 2 -
      (x t - ((∑ k ∈ Finset.range n, x k) - x t) / (n - 1 : ℚ)) ^ 2 := by
      simp [S, μ]


-- created on 2019-11-27
-- updated on 2026-10-17
