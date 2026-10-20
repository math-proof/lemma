import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  (x : Fin n → ℝ)
  (y : Fin m → ℝ)
  (t : Fin m)
-- given
  (h₀ : 0 < n)
  (h₁ : 2 ≤ m)
  (h₂ : |y t - (∑ i, x i) / (n : ℝ)| ≤ |y t - (∑ j, y j) / (m : ℝ)|) :
-- imply
  (∑ i, (x i - ((∑ i, x i) + y t) / ((n : ℝ) + 1)) ^ 2) +
    (y t - ((∑ i, x i) + y t) / ((n : ℝ) + 1)) ^ 2 +
    (∑ j, (y j - ((∑ j, y j) - y t) / ((m : ℝ) - 1)) ^ 2) -
    (y t - ((∑ j, y j) - y t) / ((m : ℝ) - 1)) ^ 2 ≤
    (∑ i, (x i - (∑ i, x i) / (n : ℝ)) ^ 2) +
    ∑ j, (y j - (∑ j, y j) / (m : ℝ)) ^ 2 := by
-- proof
  set z : ℝ := y t
  set a : ℝ := (∑ i, x i) / (n : ℝ)
  set b : ℝ := (∑ j, y j) / (m : ℝ)
  set zx : ℝ := ((∑ i, x i) + z) / ((n : ℝ) + 1)
  set zy : ℝ := ((∑ j, y j) - z) / ((m : ℝ) - 1)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h₀.ne'
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_two h₁))
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast h₁
    linarith
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hsumx : ∑ i, (x i - a) = 0 := by
    simp only [a, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  have hsumy : ∑ j, (y j - b) = 0 := by
    simp only [b, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  have haz : a - zx = (a - z) / ((n : ℝ) + 1) := by
    unfold a zx
    field_simp
    ring
  have hzzx : z - zx = (n : ℝ) * (z - a) / ((n : ℝ) + 1) := by
    unfold a zx
    field_simp
    ring
  have hbz : b - zy = (z - b) / ((m : ℝ) - 1) := by
    unfold b zy
    field_simp
    ring
  have hzzy : z - zy = (m : ℝ) * (z - b) / ((m : ℝ) - 1) := by
    unfold b zy
    field_simp
    ring
  have hx : (∑ i, (x i - zx) ^ 2) + (z - zx) ^ 2 =
    (∑ i, (x i - a) ^ 2) + (n : ℝ) / ((n : ℝ) + 1) * (z - a) ^ 2 := by
    have hxi : ∀ i, x i - zx = (x i - a) + (a - zx) := by
      intro i
      ring
    simp_rw [hxi]
    have hsq : ∀ i, ((x i - a) + (a - zx)) ^ 2 =
      (x i - a) ^ 2 + 2 * (x i - a) * (a - zx) + (a - zx) ^ 2 := by
      intro i
      ring
    simp_rw [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcross : ∑ i, (2 * (x i - a) * (a - zx)) = 0 := by
      have hcomm : ∀ i, 2 * (x i - a) * (a - zx) = (a - zx) * (2 * (x i - a)) := by
        intro i
        ring
      simp_rw [hcomm]
      rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))]
      have : ∑ i, 2 * (x i - a) = 2 * ∑ i, (x i - a) := by
        simp_rw [Finset.mul_sum]
      rw [this, hsumx]
      ring
    have hconst : ∑ i : Fin n, (a - zx) ^ 2 = (n : ℝ) * (a - zx) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hcross, hconst, haz, hzzx]
    field_simp
    ring
  have hy : (∑ j, (y j - zy) ^ 2) - (z - zy) ^ 2 =
    (∑ j, (y j - b) ^ 2) - (m : ℝ) / ((m : ℝ) - 1) * (z - b) ^ 2 := by
    have hyj : ∀ j, y j - zy = (y j - b) + (b - zy) := by
      intro j
      ring
    simp_rw [hyj]
    have hsq : ∀ j, ((y j - b) + (b - zy)) ^ 2 =
      (y j - b) ^ 2 + 2 * (y j - b) * (b - zy) + (b - zy) ^ 2 := by
      intro j
      ring
    simp_rw [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcross : ∑ j, (2 * (y j - b) * (b - zy)) = 0 := by
      have hcomm : ∀ j, 2 * (y j - b) * (b - zy) = (b - zy) * (2 * (y j - b)) := by
        intro j
        ring
      simp_rw [hcomm]
      rw [← Finset.mul_sum (Finset.univ : Finset (Fin m))]
      have : ∑ j, 2 * (y j - b) = 2 * ∑ j, (y j - b) := by
        simp_rw [Finset.mul_sum]
      rw [this, hsumy]
      ring
    have hconst : ∑ j : Fin m, (b - zy) ^ 2 = (m : ℝ) * (b - zy) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hcross, hconst, hbz, hzzy]
    field_simp
    ring
  rw [hx, add_sub_assoc, hy]
  have hsq : (z - a) ^ 2 ≤ (z - b) ^ 2 := by
    simpa [z, a, b] using sq_le_sq.mpr h₂
  have hcoef : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    rw [div_le_one hpos]
    linarith
  have hcoef' : 1 ≤ (m : ℝ) / ((m : ℝ) - 1) := by
    have hpos : 0 < (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast h₁
      linarith
    rw [one_le_div hpos]
    linarith
  have hnonneg : 0 ≤ (z - b) ^ 2 := sq_nonneg _
  have hleft : (n : ℝ) / ((n : ℝ) + 1) * (z - a) ^ 2 ≤ (z - a) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) hcoef
  have hright : (z - b) ^ 2 ≤ (m : ℝ) / ((m : ℝ) - 1) * (z - b) ^ 2 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hcoef' hnonneg
  linarith


-- created on 2019-11-28
-- updated on 2026-10-17
