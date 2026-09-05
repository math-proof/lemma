import sympy.Basic


@[main]
private lemma main
  {l u : ℕ}
  {i : Fin n}
-- given
  (h_dvd : d ∣ l) :
-- imply
  ⌈((↑(i - l) : ℤ) - (i - l)) / (d : ℚ)⌉ ≤ ⌊((↑((n - 1) ⊓ (i + u)) : ℤ) - (i - l)) / (d : ℚ)⌋ := by
-- proof
  if h_d : d = 0 then
    subst h_d
    simp
  else
    obtain ⟨q, hl⟩ := h_dvd
    have hd' : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero h_d
    have hceil_le_q : ⌈((↑(i - l) : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌉ ≤ q := by
      have hnum_le_l_z : (↑(i - l) : ℤ) - ((i : ℤ) - l) ≤ l := by
        if hle : ↑i ≤ l then
          have hzero : (↑(i - l) : ℤ) = 0 := congrArg Int.ofNat (Nat.sub_eq_zero_of_le hle)
          rw [hzero, zero_sub]
          have hneg : ((i : ℤ) - l) = -((l - i : ℤ)) := by ring
          rw [hneg, neg_neg]
          omega
        else
          have hge := (not_le.mp hle).le
          have hcast : (↑(i - l) : ℤ) = (i : ℤ) - l := by
            simp [Nat.cast_sub hge]
          rw [hcast, sub_self]
          omega
      apply Int.ceil_le.mpr
      rw [div_le_iff₀ hd']
      calc
        ((↑(i - l) : ℤ) - ((i : ℤ) - l) : ℚ) ≤ (l : ℚ) := by exact_mod_cast hnum_le_l_z
        _ = (q : ℚ) * d := by
          rw [hl]
          norm_cast
          ring_nf
    have hq_le_floor : (q : ℤ) ≤ ⌊((↑((n - 1) ⊓ (i + u)) : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌋ := by
      have hge_z : (l : ℤ) ≤ ((n - 1) ⊓ (i + u) : ℤ) - Int.subNatNat i l := by
        if hle : i ≤ l then
          simp [Int.subNatNat_eq_coe]
          omega
        else
          have hge : l ≤ i := (not_le.mp hle).le
          simp [Int.subNatNat_eq_coe]
          omega
      apply Int.le_floor.mpr
      rw [le_div_iff₀ hd']
      have hsub : (((i : ℤ) - l) : ℚ) = (Int.subNatNat i l : ℚ) := by simp
      have hmin : ((↑((n - 1) ⊓ (i + u)) : ℤ) : ℚ) = (((n - 1) ⊓ (i + u) : ℤ) : ℚ) := by
        simp [show (↑(n - 1) : ℤ) = n - 1 by omega]
      have hle : (l : ℚ) ≤ ((↑((n - 1) ⊓ (i + u)) : ℤ) - ((i : ℤ) - l) : ℚ) := by
        rw [hsub, hmin]
        exact_mod_cast hge_z
      have hq' : (q : ℚ) * d = (l : ℚ) := by
        rw [hl]
        norm_cast
        ring_nf
      simpa [hq'] using hle
    exact_mod_cast hceil_le_q.trans (Int.cast_le.mpr hq_le_floor)


-- created on 2026-07-28
