import sympy.Basic


@[path]
private lemma main
  [DecidableEq α]
  {y : α}
  {X Y : Finset α}
  {a : α → ℝ}
-- given
  (h₀ : |a y - (∑ x ∈ X, a x) / (X.card : ℝ)| ≤ |a y - (∑ z ∈ Y, a z) / (Y.card : ℝ)|)
  (h₁ : y ∈ Y)
  (h₂ : y ∉ X)
  (h₃ : 0 < X.card) :
-- imply
  (∑ x ∈ insert y X, (a x - (∑ z ∈ insert y X, a z) / ((X.card + 1 : ℕ) : ℝ)) ^ 2) +
      ∑ z ∈ Y.erase y, (a z - (∑ w ∈ Y.erase y, a w) / ((Y.card - 1 : ℕ) : ℝ)) ^ 2 ≤
    (∑ x ∈ X, (a x - (∑ z ∈ X, a z) / (X.card : ℝ)) ^ 2) +
      ∑ z ∈ Y, (a z - (∑ w ∈ Y, a w) / (Y.card : ℝ)) ^ 2 := by
-- proof
  if hm : Y.card = 1 then
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hm
    have hyz : y = z := by
      have hym : y ∈ Y := h₁
      rwa [hz, Finset.mem_singleton] at hym
    have hY : Y = {y} := by
      rw [hz, hyz]
    have hmean : (∑ w ∈ Y, a w) / (Y.card : ℝ) = a y := by
      simp [hY]
    have heq : a y = (∑ x ∈ X, a x) / (X.card : ℝ) := by
      have habs := h₀
      rw [hmean] at habs
      have hzero : |a y - (∑ x ∈ X, a x) / (X.card : ℝ)| = 0 := by
        apply le_antisymm
        · simpa using habs
        · exact abs_nonneg _
      have hsub : a y - (∑ x ∈ X, a x) / (X.card : ℝ) = 0 := abs_eq_zero.mp hzero
      linarith
    have hcard : ((insert y X).card : ℝ) = (X.card : ℝ) + 1 := by
      simp [Finset.card_insert_of_notMem h₂]
    have hsum : ∑ z ∈ insert y X, a z = (∑ z ∈ X, a z) + a y := by
      simpa [add_comm] using Finset.sum_insert (f := a) h₂
    have hmeanI : (∑ z ∈ insert y X, a z) / ((X.card + 1 : ℕ) : ℝ) = a y := by
      rw [hsum, heq]
      field_simp
      rw [Nat.cast_add, Nat.cast_one]
    rw [hY, Finset.sum_insert h₂, hmeanI, heq]
    simp [Finset.erase_singleton]
  else
    have hge : 2 ≤ Y.card := by
      have hpos : 0 < Y.card := Finset.card_pos.mpr ⟨y, h₁⟩
      omega
    set n : ℕ := X.card
    set m : ℕ := Y.card
    set S : ℝ := ∑ x ∈ X, a x
    set T : ℝ := ∑ z ∈ Y, a z
    set yv : ℝ := a y
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h₃.ne'
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hm1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m - 1 ≠ 0)
    have hcardI : (insert y X).card = n + 1 := Finset.card_insert_of_notMem h₂
    have hsumI : ∑ z ∈ insert y X, a z = S + yv := by
      simpa [S, yv, add_comm] using Finset.sum_insert (f := a) h₂
    have hsumE : ∑ w ∈ Y.erase y, a w = T - yv := by
      simpa [T, yv] using eq_sub_of_add_eq (Finset.sum_erase_add Y a h₁)
    have hsqI : ∑ x ∈ insert y X, a x ^ 2 = (∑ x ∈ X, a x ^ 2) + yv ^ 2 := by
      simpa [yv, add_comm] using Finset.sum_insert (f := fun x => a x ^ 2) h₂
    have hsqE : ∑ z ∈ Y.erase y, a z ^ 2 = (∑ z ∈ Y, a z ^ 2) - yv ^ 2 := by
      simpa [yv] using eq_sub_of_add_eq (Finset.sum_erase_add Y (fun z => a z ^ 2) h₁)
    have hsse {s : Finset α} (hs : s.card ≠ 0) :
      ∑ x ∈ s, (a x - (∑ z ∈ s, a z) / (s.card : ℝ)) ^ 2 =
        ∑ x ∈ s, a x ^ 2 - (∑ z ∈ s, a z) ^ 2 / (s.card : ℝ) := by
      have hc : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs
      have hμ : ∑ x ∈ s, ((∑ z ∈ s, a z) / (s.card : ℝ)) ^ 2 =
          (∑ z ∈ s, a z) ^ 2 / (s.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
      have hcross : ∑ x ∈ s, 2 * a x * ((∑ z ∈ s, a z) / (s.card : ℝ)) =
          2 * (∑ z ∈ s, a z) ^ 2 / (s.card : ℝ) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
        field_simp
      simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hμ, hcross]
      field_simp
      ring
    have hXn : X.card ≠ 0 := h₃.ne'
    have hYn : Y.card ≠ 0 := by omega
    have hIn : (insert y X).card ≠ 0 := by rw [hcardI]; omega
    have hEn : (Y.erase y).card ≠ 0 := by rw [Finset.card_erase_of_mem h₁]; omega
    have hIX : ∑ x ∈ insert y X, (a x - (∑ z ∈ insert y X, a z) / ((n + 1 : ℕ) : ℝ)) ^ 2 =
        (∑ x ∈ X, a x ^ 2) + yv ^ 2 - (S + yv) ^ 2 / ((n : ℝ) + 1) := by
      have hden : ((insert y X).card : ℝ) = (n : ℝ) + 1 := by
        rw [hcardI, Nat.cast_add, Nat.cast_one]
      rw [← hcardI, hsse hIn, hsqI, hsumI, hden]
    have hEY : ∑ z ∈ Y.erase y, (a z - (∑ w ∈ Y.erase y, a w) / ((m - 1 : ℕ) : ℝ)) ^ 2 =
        (∑ z ∈ Y, a z ^ 2) - yv ^ 2 - (T - yv) ^ 2 / ((m : ℝ) - 1) := by
      have hden : ((Y.erase y).card : ℝ) = (m : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem h₁, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      rw [← Finset.card_erase_of_mem h₁, hsse hEn, hsqE, hsumE, hden]
    have hX : ∑ x ∈ X, (a x - S / (n : ℝ)) ^ 2 = (∑ x ∈ X, a x ^ 2) - S ^ 2 / (n : ℝ) := by
      simpa [S, n] using hsse hXn
    have hY : ∑ z ∈ Y, (a z - T / (m : ℝ)) ^ 2 = (∑ z ∈ Y, a z ^ 2) - T ^ 2 / (m : ℝ) := by
      simpa [T, m] using hsse hYn
    have hgoal :
      ((∑ x ∈ X, a x ^ 2) + yv ^ 2 - (S + yv) ^ 2 / ((n : ℝ) + 1) +
        ((∑ z ∈ Y, a z ^ 2) - yv ^ 2 - (T - yv) ^ 2 / ((m : ℝ) - 1))) -
        (((∑ x ∈ X, a x ^ 2) - S ^ 2 / (n : ℝ)) + ((∑ z ∈ Y, a z ^ 2) - T ^ 2 / (m : ℝ))) =
        (n : ℝ) / ((n : ℝ) + 1) * (yv - S / (n : ℝ)) ^ 2 -
          (m : ℝ) / ((m : ℝ) - 1) * (yv - T / (m : ℝ)) ^ 2 := by
      have hn1 : (n : ℝ) + 1 ≠ 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact Nat.cast_ne_zero.mpr (by omega)
      have hmm : (m : ℝ) - 1 ≠ 0 := by
        rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ m)]
        exact Nat.cast_ne_zero.mpr (by omega)
      field_simp [hn0, hn1, hm0, hmm]
      ring
    have hle : (n : ℝ) / ((n : ℝ) + 1) * (yv - S / (n : ℝ)) ^ 2 ≤
        (m : ℝ) / ((m : ℝ) - 1) * (yv - T / (m : ℝ)) ^ 2 := by
      have hd : (yv - S / (n : ℝ)) ^ 2 ≤ (yv - T / (m : ℝ)) ^ 2 := by
        have habs : |yv - S / (n : ℝ)| ≤ |yv - T / (m : ℝ)| := by simpa [yv, S, T, n, m] using h₀
        have hsq : |yv - S / (n : ℝ)| ^ 2 ≤ |yv - T / (m : ℝ)| ^ 2 := by gcongr
        simpa [sq_abs] using hsq
      have hposX : 0 ≤ (yv - S / (n : ℝ)) ^ 2 := sq_nonneg _
      have hfracX : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by linarith : 0 < (n : ℝ) + 1)]
        linarith
      have hmpos : 0 < (m : ℝ) - 1 := by
        have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hge
        linarith
      have hfracY : 1 ≤ (m : ℝ) / ((m : ℝ) - 1) := by
        rw [one_le_div hmpos]
        linarith
      have h1 : (n : ℝ) / ((n : ℝ) + 1) * (yv - S / (n : ℝ)) ^ 2 ≤ (yv - S / (n : ℝ)) ^ 2 :=
        mul_le_of_le_one_left hposX hfracX
      have h2 : (yv - T / (m : ℝ)) ^ 2 ≤ (m : ℝ) / ((m : ℝ) - 1) * (yv - T / (m : ℝ)) ^ 2 := by
        have hnn : 0 ≤ (yv - T / (m : ℝ)) ^ 2 := sq_nonneg _
        simpa [one_mul] using mul_le_mul_of_nonneg_right hfracY hnn
      linarith
    rw [hIX, hEY, hX, hY]
    linarith [hgoal, hle]


-- created on 2021-03-25
-- updated on 2026-10-17
