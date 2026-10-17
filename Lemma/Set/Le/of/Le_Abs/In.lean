import sympy.Basic


@[path]
private lemma main
  {n m t : ℕ}
  {x y : ℕ → ℝ}
-- given
  (h₀ : |y t - (∑ i ∈ Finset.range n, x i) / (n : ℝ)| ≤
    |y t - (∑ j ∈ Finset.range m, y j) / (m : ℝ)|)
  (h₁ : 2 ≤ m)
  (h₂ : t < m)
  (h₃ : 0 < n) :
-- imply
  (∑ i ∈ Finset.range n, (x i - ((∑ k ∈ Finset.range n, x k) + y t) / ((n + 1 : ℕ) : ℝ)) ^ 2) +
      (y t - ((∑ k ∈ Finset.range n, x k) + y t) / ((n + 1 : ℕ) : ℝ)) ^ 2 +
      ((∑ j ∈ Finset.range m, (y j - ((∑ k ∈ Finset.range m, y k) - y t) / ((m - 1 : ℕ) : ℝ)) ^ 2) -
        (y t - ((∑ k ∈ Finset.range m, y k) - y t) / ((m - 1 : ℕ) : ℝ)) ^ 2) ≤
    (∑ i ∈ Finset.range n, (x i - (∑ k ∈ Finset.range n, x k) / (n : ℝ)) ^ 2) +
      ∑ j ∈ Finset.range m, (y j - (∑ k ∈ Finset.range m, y k) / (m : ℝ)) ^ 2 := by
-- proof
  set S : ℝ := ∑ i ∈ Finset.range n, x i
  set T : ℝ := ∑ j ∈ Finset.range m, y j
  set yt : ℝ := y t
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h₃.ne'
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : m ≠ 0)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hmm : (m : ℝ) - 1 ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ m)]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hXt : t ∈ Finset.range m := Finset.mem_range.mpr h₂
  have hsq (s : Finset ℕ) (f : ℕ → ℝ) (μ : ℝ) :
    ∑ i ∈ s, (f i - μ) ^ 2 = ∑ i ∈ s, f i ^ 2 - 2 * μ * ∑ i ∈ s, f i + (s.card : ℝ) * μ ^ 2 := by
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp [mul_comm, mul_left_comm]
    rw [Finset.sum_mul, ← Finset.mul_sum]
  have hXadd :
    (∑ i ∈ Finset.range n, (x i - (S + yt) / ((n + 1 : ℕ) : ℝ)) ^ 2) +
      (yt - (S + yt) / ((n + 1 : ℕ) : ℝ)) ^ 2 =
        (∑ i ∈ Finset.range n, x i ^ 2) + yt ^ 2 - (S + yt) ^ 2 / ((n : ℝ) + 1) := by
    have hcard : ((Finset.range n).card : ℝ) = n := by simp
    dsimp only [S]
    rw [hsq (Finset.range n) x (((∑ i ∈ Finset.range n, x i) + yt) / ((n + 1 : ℕ) : ℝ)), hcard, sub_sq]
    field_simp [hn1]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hXold :
    ∑ i ∈ Finset.range n, (x i - S / (n : ℝ)) ^ 2 =
      (∑ i ∈ Finset.range n, x i ^ 2) - S ^ 2 / (n : ℝ) := by
    have hcard : ((Finset.range n).card : ℝ) = n := by simp
    rw [hsq (Finset.range n) x (S / (n : ℝ)), hcard]
    field_simp [hn0]
    ring
  have hYnew :
    (∑ j ∈ Finset.range m, (y j - (T - yt) / ((m - 1 : ℕ) : ℝ)) ^ 2) -
      (yt - (T - yt) / ((m - 1 : ℕ) : ℝ)) ^ 2 =
      (∑ j ∈ (Finset.range m).erase t, y j ^ 2) - (T - yt) ^ 2 / ((m : ℝ) - 1) := by
    have hcard : (((Finset.range m).erase t).card : ℝ) = (m : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hXt, Finset.card_range, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hsum : ∑ j ∈ (Finset.range m).erase t, y j = T - yt := by
      simpa [T, yt] using eq_sub_of_add_eq (Finset.sum_erase_add (Finset.range m) y hXt)
    have hsplit : ∑ j ∈ Finset.range m, (y j - (T - yt) / ((m - 1 : ℕ) : ℝ)) ^ 2 =
        (∑ j ∈ (Finset.range m).erase t, (y j - (T - yt) / ((m - 1 : ℕ) : ℝ)) ^ 2) +
          (yt - (T - yt) / ((m - 1 : ℕ) : ℝ)) ^ 2 := by
      simpa [yt, add_comm] using
        (Finset.sum_erase_add (Finset.range m) (fun j => (y j - (T - yt) / ((m - 1 : ℕ) : ℝ)) ^ 2) hXt).symm
    dsimp only [T]
    rw [hsplit, add_sub_cancel_right,
      hsq ((Finset.range m).erase t) y (((∑ j ∈ Finset.range m, y j) - yt) / ((m - 1 : ℕ) : ℝ)), hcard, hsum]
    field_simp [hmm]
    simp only [Nat.cast_one, Nat.cast_sub (show 1 ≤ m by omega), T]
    ring
  have hYold :
    ∑ j ∈ Finset.range m, (y j - T / (m : ℝ)) ^ 2 =
      (∑ j ∈ Finset.range m, y j ^ 2) - T ^ 2 / (m : ℝ) := by
    have hcard : ((Finset.range m).card : ℝ) = m := by simp
    rw [hsq (Finset.range m) y (T / (m : ℝ)), hcard]
    field_simp [hm0]
    ring
  have hsqE : ∑ j ∈ (Finset.range m).erase t, y j ^ 2 = (∑ j ∈ Finset.range m, y j ^ 2) - yt ^ 2 := by
    simpa [yt] using eq_sub_of_add_eq (Finset.sum_erase_add (Finset.range m) (fun j => y j ^ 2) hXt)
  have hgoal :
    ((∑ i ∈ Finset.range n, x i ^ 2) + yt ^ 2 - (S + yt) ^ 2 / ((n : ℝ) + 1) +
      ((∑ j ∈ Finset.range m, y j ^ 2) - yt ^ 2 - (T - yt) ^ 2 / ((m : ℝ) - 1))) -
      (((∑ i ∈ Finset.range n, x i ^ 2) - S ^ 2 / (n : ℝ)) +
        ((∑ j ∈ Finset.range m, y j ^ 2) - T ^ 2 / (m : ℝ))) =
        (n : ℝ) / ((n : ℝ) + 1) * (yt - S / (n : ℝ)) ^ 2 -
          (m : ℝ) / ((m : ℝ) - 1) * (yt - T / (m : ℝ)) ^ 2 := by
    field_simp [hn0, hn1, hm0, hmm]
    ring
  have hle : (n : ℝ) / ((n : ℝ) + 1) * (yt - S / (n : ℝ)) ^ 2 ≤
      (m : ℝ) / ((m : ℝ) - 1) * (yt - T / (m : ℝ)) ^ 2 := by
    have hd : (yt - S / (n : ℝ)) ^ 2 ≤ (yt - T / (m : ℝ)) ^ 2 := by
      have habs : |yt - S / (n : ℝ)| ≤ |yt - T / (m : ℝ)| := by simpa [yt, S, T] using h₀
      have hsqa : |yt - S / (n : ℝ)| ^ 2 ≤ |yt - T / (m : ℝ)| ^ 2 := by gcongr
      simpa [sq_abs] using hsqa
    have hposX : 0 ≤ (yt - S / (n : ℝ)) ^ 2 := sq_nonneg _
    have hfracX : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith : 0 < (n : ℝ) + 1)]
      linarith
    have hmpos : 0 < (m : ℝ) - 1 := by
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast h₁
      linarith
    have hfracY : 1 ≤ (m : ℝ) / ((m : ℝ) - 1) := by
      rw [one_le_div hmpos]
      linarith
    have hleft : (n : ℝ) / ((n : ℝ) + 1) * (yt - S / (n : ℝ)) ^ 2 ≤ (yt - S / (n : ℝ)) ^ 2 :=
      mul_le_of_le_one_left hposX hfracX
    have hright : (yt - T / (m : ℝ)) ^ 2 ≤ (m : ℝ) / ((m : ℝ) - 1) * (yt - T / (m : ℝ)) ^ 2 := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hfracY (sq_nonneg (yt - T / (m : ℝ)))
    linarith
  rw [hXadd, hYnew, hsqE, hXold, hYold]
  linarith [hgoal, hle]


-- created on 2026-10-11
-- updated on 2026-10-17
