import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic
import Notation.Algebra.Power


@[path]
private lemma main
  {n t : ℕ}
  {x : ℕ → ℚ}
-- given
  (h₀ : n ≥ 2)
  (h₁ : t < n) :
-- imply
  ((∑ i < n, ∑ j < i, (x i - x j)²) -
      ∑ i < n, (x i - x t)²) / (n - 1 : ℚ) =
    ∑ i < n,
        (x i - ((∑ k < n, x k) - x t) / (n - 1 : ℚ))² -
      (x t - ((∑ k < n, x k) - x t) / (n - 1 : ℚ))² := by
-- proof
  simp only [Nat.Iio_eq_range]
  set S : ℚ := (Finset.range n).sum (fun k => x k)
  set Q : ℚ := (Finset.range n).sum (fun k => x k ^ 2)
  have hcast : (↑(n - 1) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (le_trans (by norm_num : 1 ≤ 2) h₀), Nat.cast_one]
  have hsq : (Finset.range n).sum (fun i => (Finset.range i).sum (fun j => (x i - x j)²)) =
    (n : ℚ) * Q - S² := by
    have hstep : ∀ m : ℕ, (Finset.range m).sum (fun i => (Finset.range i).sum (fun j => (x i - x j)²)) =
      (m : ℚ) * (Finset.range m).sum (fun i => x i ^ 2) - ((Finset.range m).sum (fun i => x i))² := by
      intro m
      induction m with
      | zero =>
        simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => x i ^ 2),
          Finset.sum_range_succ (fun i => x i), ih, Nat.cast_succ]
        have hrow : (Finset.range m).sum (fun j => (x m - x j)²) =
          (m : ℚ) * x m ^ 2 - 2 * x m * (Finset.range m).sum (fun j => x j) +
          (Finset.range m).sum (fun j => x j ^ 2) := by
          trans (Finset.range m).sum (fun j => (x m ^ 2 - 2 * x m * x j + x j ^ 2))
          ·
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ← Finset.mul_sum]
        rw [hrow]
        ring
    simpa [S, Q] using hstep n
  have hdev : (Finset.range n).sum (fun i => (x i - x t)²) =
    Q - 2 * x t * S + (n : ℚ) * x t ^ 2 := by
    trans (Finset.range n).sum (fun i => (x i ^ 2 - 2 * x t * x i + x t ^ 2))
    ·
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
  have hnz : (n : ℚ) - 1 ≠ 0 := by
    rw [← hcast]
    exact_mod_cast show n - 1 ≠ 0 by omega
  have hnum : (Finset.range n).sum (fun i => (Finset.range i).sum (fun j => (x i - x j)²)) -
    (Finset.range n).sum (fun i => (x i - x t)²) =
    ((n : ℚ) - 1) * (Q - x t ^ 2) - (S - x t)² := by
    rw [hsq, hdev]
    ring
  set μ : ℚ := (S - x t) / ((n : ℚ) - 1)
  have ht : t ∈ Finset.range n := Finset.mem_range.mpr h₁
  have hrest : (Finset.range n).sum (fun i => (x i - μ)²) - (x t - μ)² =
    ∑ i ∈ (Finset.range n).erase t, (x i - μ)² := by
    rw [← Finset.add_sum_erase (s := Finset.range n) (f := fun i => (x i - μ)²) ht]
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
  have hsse : ∑ i ∈ (Finset.range n).erase t, (x i - μ)² =
    Q - x t ^ 2 - (S - x t)² / ((n : ℚ) - 1) := by
    trans ∑ i ∈ (Finset.range n).erase t, (x i ^ 2 - 2 * μ * x i + μ²)
    ·
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul,
      ← Finset.mul_sum, hx, hx2, hcast]
    unfold μ
    field_simp [hnz]
    ring
  calc
    _ = (((n : ℚ) - 1) * (Q - x t ^ 2) - (S - x t)²) / ((n : ℚ) - 1) := by
      rw [hnum]
    _ = Q - x t ^ 2 - (S - x t)² / ((n : ℚ) - 1) := by
      field_simp [hnz]
    _ = ∑ i ∈ (Finset.range n).erase t, (x i - μ)² := by
      rw [hsse]
    _ = (Finset.range n).sum (fun i => (x i - μ)²) - (x t - μ)² := by
      rw [hrest]
    _ = (Finset.range n).sum (fun i => (x i - ((Finset.range n).sum (fun k => x k) - x t) / (n - 1 : ℚ))²) -
      (x t - ((Finset.range n).sum (fun k => x k) - x t) / (n - 1 : ℚ))² := by
      simp [S, μ]


-- created on 2019-11-27
-- updated on 2026-11-26
