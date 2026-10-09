import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.BigOperators.Intervals
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k * k = n * (x + 1) ^ (n - 1) * x := by
-- proof
  have hd : ∀ k r : ℕ, ((k.descFactorial (r + 1) : ℕ) : ℝ) = ((k : ℝ) - r) * (k.descFactorial r : ℕ) := by
    intro k r
    rw [Nat.descFactorial_succ]
    rcases le_or_gt r k with h | h
    · push_cast [Nat.cast_sub h]
      ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]
      simp
  have hS : ∀ r : ℕ, r ≤ n → ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
      (n.descFactorial r : ℕ) * x ^ r * (x + 1) ^ (n - r) := by
    intro r hr
    have e : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
        if r ≤ k then (r.factorial : ℝ) * n.choose r * ((n - r).choose (k - r)) * x ^ k else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      split_ifs with h
      · rw [Nat.descFactorial_eq_factorial_mul_choose]
        have := Nat.choose_mul (n := n) (k := k) (s := r) h
        have h' : (n.choose k : ℝ) * (k.choose r) = n.choose r * (n - r).choose (k - r) := by exact_mod_cast this
        push_cast
        linear_combination (r.factorial : ℝ) * x ^ k * h'
      · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]
        simp
    have hset : (Finset.range (n + 1)).filter (fun k => r ≤ k) = Finset.Ico r (n + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [Finset.sum_congr rfl e, ← Finset.sum_filter, hset, Finset.sum_Ico_eq_sum_range,
      show n + 1 - r = (n - r) + 1 by omega, add_pow, Finset.mul_sum, Nat.descFactorial_eq_factorial_mul_choose]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left, pow_add, one_pow]
    push_cast
    ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 := hS 1 hn
  rw [hd n 0, Nat.descFactorial_zero] at h1
  calc _ = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial 1 : ℕ) * x ^ k :=
        Finset.sum_congr rfl fun k _ => by rw [hd k 0, Nat.descFactorial_zero]; push_cast; ring
    _ = _ := by rw [h1]; push_cast; ring


@[path]
private lemma deux
  {n : ℕ}
  {x : ℝ}
-- given
  (h : 2 ≤ n) :
-- imply
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2 * x ^ k = n * x * (n * x + 1) * (x + 1) ^ (n - 2) := by
-- proof
  have hd : ∀ k r : ℕ, ((k.descFactorial (r + 1) : ℕ) : ℝ) = ((k : ℝ) - r) * (k.descFactorial r : ℕ) := by
    intro k r
    rw [Nat.descFactorial_succ]
    rcases le_or_gt r k with h | h
    · push_cast [Nat.cast_sub h]
      ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]
      simp
  have hS : ∀ r : ℕ, r ≤ n → ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
      (n.descFactorial r : ℕ) * x ^ r * (x + 1) ^ (n - r) := by
    intro r hr
    have e : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
        if r ≤ k then (r.factorial : ℝ) * n.choose r * ((n - r).choose (k - r)) * x ^ k else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      split_ifs with h
      · rw [Nat.descFactorial_eq_factorial_mul_choose]
        have := Nat.choose_mul (n := n) (k := k) (s := r) h
        have h' : (n.choose k : ℝ) * (k.choose r) = n.choose r * (n - r).choose (k - r) := by exact_mod_cast this
        push_cast
        linear_combination (r.factorial : ℝ) * x ^ k * h'
      · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]
        simp
    have hset : (Finset.range (n + 1)).filter (fun k => r ≤ k) = Finset.Ico r (n + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [Finset.sum_congr rfl e, ← Finset.sum_filter, hset, Finset.sum_Ico_eq_sum_range,
      show n + 1 - r = (n - r) + 1 by omega, add_pow, Finset.mul_sum, Nat.descFactorial_eq_factorial_mul_choose]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left, pow_add, one_pow]
    push_cast
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  calc _ = ∑ k ∈ Finset.range (m + 2 + 1), (1 * (((m + 2).choose k : ℝ) * (k.descFactorial 2 : ℕ) * x ^ k) + 1 * (((m + 2).choose k : ℝ) * (k.descFactorial 1 : ℕ) * x ^ k)) :=
        Finset.sum_congr rfl fun k _ => by rw [hd k 1, hd k 0, Nat.descFactorial_zero]; push_cast; ring
    _ = 1 * ∑ k ∈ Finset.range (m + 2 + 1), (((m + 2).choose k : ℝ) * (k.descFactorial 2 : ℕ) * x ^ k) + 1 * ∑ k ∈ Finset.range (m + 2 + 1), (((m + 2).choose k : ℝ) * (k.descFactorial 1 : ℕ) * x ^ k) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
        rw [hS 2 (by omega), hS 1 (by omega)]
        rw [hd (m + 2) 1, hd (m + 2) 0, Nat.descFactorial_zero]
        simp only [show m + 2 - 2 = m + 0 by omega, show m + 2 - 1 = m + 1 by omega]
        simp only [one_mul]
        push_cast
        ring


@[path]
private lemma trois
  {n : ℕ}
  {x : ℝ}
-- given
  (h : 3 ≤ n) :
-- imply
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 3 * x ^ k = (ascPochhammer ℝ 3).eval ((n : ℝ) * x) * (x + 1) ^ (n - 3) - n * x * (x + 1) ^ (n - 2) := by
-- proof
  have hd : ∀ k r : ℕ, ((k.descFactorial (r + 1) : ℕ) : ℝ) = ((k : ℝ) - r) * (k.descFactorial r : ℕ) := by
    intro k r
    rw [Nat.descFactorial_succ]
    rcases le_or_gt r k with h | h
    · push_cast [Nat.cast_sub h]
      ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]
      simp
  have hS : ∀ r : ℕ, r ≤ n → ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
      (n.descFactorial r : ℕ) * x ^ r * (x + 1) ^ (n - r) := by
    intro r hr
    have e : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
        if r ≤ k then (r.factorial : ℝ) * n.choose r * ((n - r).choose (k - r)) * x ^ k else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      split_ifs with h
      · rw [Nat.descFactorial_eq_factorial_mul_choose]
        have := Nat.choose_mul (n := n) (k := k) (s := r) h
        have h' : (n.choose k : ℝ) * (k.choose r) = n.choose r * (n - r).choose (k - r) := by exact_mod_cast this
        push_cast
        linear_combination (r.factorial : ℝ) * x ^ k * h'
      · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]
        simp
    have hset : (Finset.range (n + 1)).filter (fun k => r ≤ k) = Finset.Ico r (n + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [Finset.sum_congr rfl e, ← Finset.sum_filter, hset, Finset.sum_Ico_eq_sum_range,
      show n + 1 - r = (n - r) + 1 by omega, add_pow, Finset.mul_sum, Nat.descFactorial_eq_factorial_mul_choose]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left, pow_add, one_pow]
    push_cast
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  calc _ = ∑ k ∈ Finset.range (m + 3 + 1), (1 * (((m + 3).choose k : ℝ) * (k.descFactorial 3 : ℕ) * x ^ k) + 3 * (((m + 3).choose k : ℝ) * (k.descFactorial 2 : ℕ) * x ^ k) + 1 * (((m + 3).choose k : ℝ) * (k.descFactorial 1 : ℕ) * x ^ k)) :=
        Finset.sum_congr rfl fun k _ => by rw [hd k 2, hd k 1, hd k 0, Nat.descFactorial_zero]; push_cast; ring
    _ = 1 * ∑ k ∈ Finset.range (m + 3 + 1), (((m + 3).choose k : ℝ) * (k.descFactorial 3 : ℕ) * x ^ k) + 3 * ∑ k ∈ Finset.range (m + 3 + 1), (((m + 3).choose k : ℝ) * (k.descFactorial 2 : ℕ) * x ^ k) + 1 * ∑ k ∈ Finset.range (m + 3 + 1), (((m + 3).choose k : ℝ) * (k.descFactorial 1 : ℕ) * x ^ k) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
        rw [hS 3 (by omega), hS 2 (by omega), hS 1 (by omega)]
        rw [hd (m + 3) 2, hd (m + 3) 1, hd (m + 3) 0, Nat.descFactorial_zero]
        simp only [show m + 3 - 3 = m + 0 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega]
        simp only [ascPochhammer_succ_right, ascPochhammer_zero, Polynomial.eval_mul, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_natCast, one_mul]
        push_cast
        ring


@[path]
private lemma quatre
  {n : ℕ}
  {x : ℝ}
-- given
  (h : 4 ≤ n) :
-- imply
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 4 * x ^ k = (ascPochhammer ℝ 4).eval ((n : ℝ) * x) * (x + 1) ^ (n - 4) - n * x * ((4 * n - 1) * x + 5) * (x + 1) ^ (n - 3) := by
-- proof
  have hd : ∀ k r : ℕ, ((k.descFactorial (r + 1) : ℕ) : ℝ) = ((k : ℝ) - r) * (k.descFactorial r : ℕ) := by
    intro k r
    rw [Nat.descFactorial_succ]
    rcases le_or_gt r k with h | h
    · push_cast [Nat.cast_sub h]
      ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]
      simp
  have hS : ∀ r : ℕ, r ≤ n → ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
      (n.descFactorial r : ℕ) * x ^ r * (x + 1) ^ (n - r) := by
    intro r hr
    have e : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.descFactorial r : ℕ) * x ^ k =
        if r ≤ k then (r.factorial : ℝ) * n.choose r * ((n - r).choose (k - r)) * x ^ k else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      split_ifs with h
      · rw [Nat.descFactorial_eq_factorial_mul_choose]
        have := Nat.choose_mul (n := n) (k := k) (s := r) h
        have h' : (n.choose k : ℝ) * (k.choose r) = n.choose r * (n - r).choose (k - r) := by exact_mod_cast this
        push_cast
        linear_combination (r.factorial : ℝ) * x ^ k * h'
      · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]
        simp
    have hset : (Finset.range (n + 1)).filter (fun k => r ≤ k) = Finset.Ico r (n + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [Finset.sum_congr rfl e, ← Finset.sum_filter, hset, Finset.sum_Ico_eq_sum_range,
      show n + 1 - r = (n - r) + 1 by omega, add_pow, Finset.mul_sum, Nat.descFactorial_eq_factorial_mul_choose]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left, pow_add, one_pow]
    push_cast
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  calc _ = ∑ k ∈ Finset.range (m + 4 + 1), (1 * (((m + 4).choose k : ℝ) * (k.descFactorial 4 : ℕ) * x ^ k) + 6 * (((m + 4).choose k : ℝ) * (k.descFactorial 3 : ℕ) * x ^ k) + 7 * (((m + 4).choose k : ℝ) * (k.descFactorial 2 : ℕ) * x ^ k) + 1 * (((m + 4).choose k : ℝ) * (k.descFactorial 1 : ℕ) * x ^ k)) :=
        Finset.sum_congr rfl fun k _ => by rw [hd k 3, hd k 2, hd k 1, hd k 0, Nat.descFactorial_zero]; push_cast; ring
    _ = 1 * ∑ k ∈ Finset.range (m + 4 + 1), (((m + 4).choose k : ℝ) * (k.descFactorial 4 : ℕ) * x ^ k) + 6 * ∑ k ∈ Finset.range (m + 4 + 1), (((m + 4).choose k : ℝ) * (k.descFactorial 3 : ℕ) * x ^ k) + 7 * ∑ k ∈ Finset.range (m + 4 + 1), (((m + 4).choose k : ℝ) * (k.descFactorial 2 : ℕ) * x ^ k) + 1 * ∑ k ∈ Finset.range (m + 4 + 1), (((m + 4).choose k : ℝ) * (k.descFactorial 1 : ℕ) * x ^ k) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
        rw [hS 4 (by omega), hS 3 (by omega), hS 2 (by omega), hS 1 (by omega)]
        rw [hd (m + 4) 3, hd (m + 4) 2, hd (m + 4) 1, hd (m + 4) 0, Nat.descFactorial_zero]
        simp only [show m + 4 - 4 = m + 0 by omega, show m + 4 - 3 = m + 1 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 1 = m + 3 by omega]
        simp only [ascPochhammer_succ_right, ascPochhammer_zero, Polynomial.eval_mul, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_natCast, one_mul]
        push_cast
        ring


-- created on 2021-11-25
