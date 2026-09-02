import stdlib.Slice
import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Int.Sign.eq.Neg1.of.Lt_0
open Int Slice


private lemma mem_sliced_indices_pos
  {start stop step : ℕ}
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (hmem : x ∈ Nat.sliced_indices h_start h_stop h_step) :
-- imply
  ∃ k, x.val = start + k * step := by
-- proof
  unfold Nat.sliced_indices at hmem
  rw [List.mem_cons] at hmem
  obtain h_head | h_tail := hmem
  ·
    refine ⟨0, ?_⟩
    simpa using congrArg Fin.val h_head
  ·
    split_ifs at h_tail with h_if
    ·
      obtain ⟨k, hk⟩ := mem_sliced_indices_pos h_if h_stop h_step x h_tail
      refine ⟨k + 1, ?_⟩
      rw [hk]
      simp [Nat.add_mul, Nat.add_comm, Nat.add_assoc]
    ·
      simp at h_tail


private lemma mem_sliced_indices_pos_lt_stop
  {start stop step : ℕ}
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (hmem : x ∈ Nat.sliced_indices h_start h_stop h_step) :
-- imply
  x.val < stop := by
-- proof
  unfold Nat.sliced_indices at hmem
  rw [List.mem_cons] at hmem
  obtain h_head | h_tail := hmem
  ·
    simpa using congrArg Fin.val h_head ▸ h_start
  ·
    split_ifs at h_tail with h_if
    ·
      exact mem_sliced_indices_pos_lt_stop h_if h_stop h_step x h_tail
    ·
      simp at h_tail


private lemma mem_sliced_indices_pos_go
  {start stop step : ℕ}
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (k : ℕ)
  (hk : x.val = start + k * step)
  (h_lt : x.val < stop) :
-- imply
  x ∈ Nat.sliced_indices h_start h_stop h_step := by
-- proof
  induction k with
  | zero =>
    unfold Nat.sliced_indices
    rw [List.mem_cons]
    apply Or.inl (Fin.ext ?_)
    simpa [zero_mul, add_zero] using hk
  | succ k ih =>
    unfold Nat.sliced_indices
    rw [List.mem_cons]
    refine Or.inr ?_
    if h_if : start + step < stop then
      rw [dif_pos h_if]
      apply mem_sliced_indices_pos_go _ h_stop h_step x k _ h_lt
      rw [hk]
      ring
    else
      exfalso
      rw [hk] at h_lt
      apply not_le.mpr h_lt
      calc
        stop ≤ start + step := le_of_not_gt h_if
        _ ≤ start + (k + 1) * step := by
          gcongr
          have h1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left step h1


private lemma mem_sliced_indices_pos_of_eq_add_mul
  {start stop step : ℕ}
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (hk : ∃ k, x.val = start + k * step)
  (h_lt : x.val < stop) :
-- imply
  x ∈ Nat.sliced_indices h_start h_stop h_step := by
-- proof
  obtain ⟨k, hk⟩ := hk
  exact mem_sliced_indices_pos_go h_start h_stop h_step x k hk h_lt


private lemma mem_sliced_indices_neg_go
  {start stop step : ℕ}
-- given
  (h_stop : stop < start)
  (h_start : start ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (k : ℕ)
  (hk : x.val + k * step + 1 = start)
  (h_ge : stop ≤ x.val) :
-- imply
  x ∈ Nat.sliced_indices' h_stop h_start h_step := by
-- proof
  induction k with
  | zero =>
    unfold Nat.sliced_indices'
    rw [List.mem_cons]
    apply Or.inl (Fin.ext ?_)
    grind
  | succ k ih =>
    unfold Nat.sliced_indices'
    rw [List.mem_cons]
    refine Or.inr ?_
    if h_if : start - step > stop then
      rw [dif_pos h_if]
      apply mem_sliced_indices_neg_go h_if (by omega) h_step x k _ h_ge
      grind
    else
      grind


private lemma mem_sliced_indices_neg_of_eq
  {start stop step : ℕ}
-- given
  (h_stop : stop < start)
  (h_start : start ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (hk : ∃ k, x.val + k * step + 1 = start)
  (h_ge : stop ≤ x.val) :
-- imply
  x ∈ Nat.sliced_indices' h_stop h_start h_step := by
-- proof
  obtain ⟨k, hk⟩ := hk
  exact mem_sliced_indices_neg_go h_stop h_start h_step x k hk h_ge


private lemma mem_sliced_indices_neg
  {start stop step : ℕ}
-- given
  (h_stop : stop < start)
  (h_start : start ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (hmem : x ∈ Nat.sliced_indices' h_stop h_start h_step) :
-- imply
  ∃ k, x.val + k * step + 1 = start := by
-- proof
  unfold Nat.sliced_indices' at hmem
  rw [List.mem_cons] at hmem
  obtain h_head | h_tail := hmem
  ·
    refine ⟨0, ?_⟩
    have hx_eq : x.val = start - 1 := congrArg Fin.val h_head
    omega
  ·
    split_ifs at h_tail with h_if
    ·
      obtain ⟨k, hk⟩ := mem_sliced_indices_neg h_if (by omega) h_step x h_tail
      refine ⟨k + 1, ?_⟩
      calc
        x.val + (k + 1) * step + 1 = x.val + k * step + 1 + step := by ring
        _ = (start - step) + step := by rw [hk]
        _ = start := Nat.sub_add_cancel (by omega)
    ·
      simp at h_tail


private lemma mem_sliced_indices_neg_ge_stop
  {start stop step : ℕ}
-- given
  (h_stop : stop < start)
  (h_start : start ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (hmem : x ∈ Nat.sliced_indices' h_stop h_start h_step) :
-- imply
  stop ≤ x.val := by
-- proof
  unfold Nat.sliced_indices' at hmem
  rw [List.mem_cons] at hmem
  obtain h_head | h_tail := hmem
  ·
    have hx_eq : x.val = start - 1 := congrArg Fin.val h_head
    omega
  ·
    split_ifs at h_tail with h_if
    ·
      exact mem_sliced_indices_neg_ge_stop h_if (by omega) h_step x h_tail
    ·
      simp at h_tail


private lemma mem_sliced_indices_neg_lt_start
  {start stop step : ℕ}
-- given
  (h_stop : stop < start)
  (h_start : start ≤ n)
  (h_step : step > 0)
  (x : Fin n)
  (hmem : x ∈ Nat.sliced_indices' h_stop h_start h_step) :
-- imply
  x.val < start := by
-- proof
  obtain ⟨k, hk⟩ := mem_sliced_indices_neg h_stop h_start h_step x hmem
  omega


private lemma int_add_mul_emod
-- given
  (m : ℤ) (k : ℤ) (d : ℤ) :
-- imply
  (m + k * d) % d = m % d := by
-- proof
  simp [Int.add_emod]


private lemma int_mod_eq_zero_of_add_mod_eq
  {start j d : ℤ}
-- given
  (hd : 0 < d)
  (h : (start + j) % d = start % d) :
-- imply
  j % d = 0 := by
-- proof
  set a := start % d
  set b := j % d
  have h' : (a + b) % d = a := by simpa [Int.add_emod, Int.emod_emod, a, b] using h
  have ha : 0 ≤ a ∧ a < d := ⟨Int.emod_nonneg start (ne_of_gt hd), Int.emod_lt_of_pos start hd⟩
  have hb : 0 ≤ b ∧ b < d := ⟨Int.emod_nonneg j (ne_of_gt hd), Int.emod_lt_of_pos j hd⟩
  if hb0 : b = 0 then
    simp [hb0, b]
  else
    have hb_pos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
    if hab_lt : a + b < d then
      rw [Int.emod_eq_of_lt (by omega) hab_lt] at h'
      omega
    else
      have hab_ge : d ≤ a + b := by omega
      have hb' : b = d * ((a + b) / d) := by linarith [Int.emod_add_mul_ediv (a + b) d, h']
      have hquot1 : (a + b) / d = 1 := by
        have hlo : 1 ≤ (a + b) / d := by
          rw [Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < d)]
          omega
        have hhi : (a + b) / d ≤ 1 := by
          have hbound : a + b < 2 * d := by omega
          have : (a + b) / d < 2 :=
            (Int.ediv_lt_iff_lt_mul (by omega : (0 : ℤ) < d)).mpr (by linarith)
          omega
        omega
      have : b = d := by simpa [hquot1] using hb'
      exact absurd this (ne_of_lt hb.2)


private lemma nat_mod_eq_zero_of_add_mod_eq
  {start j step : ℕ}
-- given
  (h_step : 0 < step)
  (h : (start + j) % step = start % step) :
-- imply
  j % step = 0 := by
-- proof
  have hj := int_mod_eq_zero_of_add_mod_eq (show (0 : ℤ) < (step : ℤ) from Nat.cast_pos.mpr h_step) (show ((start : ℤ) + j) % (step : ℤ) = (start : ℤ) % (step : ℤ) by exact_mod_cast h)
  exact_mod_cast hj


private lemma exists_eq_mul_of_mod_eq_zero
  {j step : ℕ}
-- given
  (_h_step : 0 < step)
  (h : j % step = 0) :
-- imply
  ∃ k, j = k * step :=
-- proof
  ⟨j / step, Eq.symm (Nat.mul_comm step (j / step) ▸ Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h))⟩


private lemma mem_sliced_indices_one
  {start stop : ℕ}
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (x : Fin n)
  (h_start_le : start ≤ x.val)
  (h_x_lt_stop : x.val < stop) :
-- imply
  x ∈ Nat.sliced_indices h_start h_stop Nat.one_pos := by
-- proof
  unfold Nat.sliced_indices
  rw [List.mem_cons]
  if hx_eq : x.val = start then
    exact Or.inl (Fin.ext hx_eq)
  else
    refine Or.inr ?_
    split_ifs with h_if
    ·
      exact mem_sliced_indices_one h_if h_stop x (by omega) h_x_lt_stop
    ·
      exfalso
      omega


private lemma mem_sliced_indices_neg_one
  {start stop : ℕ}
-- given
  (h_stop : stop < start)
  (h_start : start ≤ n)
  (x : Fin n)
  (h_stop_le : stop ≤ x.val)
  (h_x_lt_start : x.val < start) :
-- imply
  x ∈ Nat.sliced_indices' h_stop h_start Nat.one_pos := by
-- proof
  unfold Nat.sliced_indices'
  rw [List.mem_cons]
  if hx_eq : x.val + 1 = start then
    refine Or.inl (Fin.ext ?_)
    grind
  else
    refine Or.inr ?_
    split_ifs with h_if
    ·
      exact mem_sliced_indices_neg_one h_if (by omega) x (by omega) (by omega)
    ·
      exfalso
      omega


private lemma slice_range_step_one_mem
  {a b : ℤ}
-- given
  (h_start_lt : (Add_Mul_DivSub1Sign_2 n a).toNat < (Add_Mul_DivSub1Sign_2 n b).toNat.min n)
  (h_stop_le : (Add_Mul_DivSub1Sign_2 n b).toNat.min n ≤ n)
  (x : Fin n)
  (h_start_le : (Add_Mul_DivSub1Sign_2 n a).toNat ≤ x.val)
  (h_x_lt_stop : x.val < (Add_Mul_DivSub1Sign_2 n b).toNat.min n) :
-- imply
  x ∈ Slice.range ⟨a, b, (1 : ℤ)⟩ n := by
-- proof
  unfold Slice.range
  dsimp [Int.ofNat_one]
  split_ifs
  ·
    exfalso
    omega
  ·
    exact mem_sliced_indices_one h_start_lt h_stop_le x h_start_le h_x_lt_stop


private lemma slice_range_step_succ_mem
  {a b : ℤ}
  {step : ℕ}
-- given
  (h_start_lt : (Add_Mul_DivSub1Sign_2 n a).toNat < (Add_Mul_DivSub1Sign_2 n b).toNat.min n)
  (h_stop_le : (Add_Mul_DivSub1Sign_2 n b).toNat.min n ≤ n)
  (x : Fin n)
  (h_mem : x ∈ Nat.sliced_indices h_start_lt h_stop_le (Nat.succ_pos step)) :
-- imply
  x ∈ Slice.range ⟨a, b, Int.ofNat (step + 1)⟩ n := by
-- proof
  simp only [Slice.range]
  split_ifs
  ·
    exact absurd (by assumption) (not_le.mpr h_start_lt)
  ·
    exact h_mem


private lemma slice_range_sign_neg_one_mem
  {a b : ℤ}
-- given
  (h_stop_lt : (Add_Mul_DivSub1Sign_2 n b + 1).toNat < (Add_Mul_DivSub1Sign_2 n a + 1).toNat.min n)
  (h_start_le : (Add_Mul_DivSub1Sign_2 n a + 1).toNat.min n ≤ n)
  (x : Fin n)
  (h_stop_le : (Add_Mul_DivSub1Sign_2 n b + 1).toNat ≤ x.val)
  (h_x_lt_start : x.val < (Add_Mul_DivSub1Sign_2 n a + 1).toNat.min n) :
-- imply
  x ∈ Slice.range ⟨a, b, (-1 : ℤ)⟩ n := by
-- proof
  unfold Slice.range
  dsimp [Slice.step, Slice.mk]
  split
  ·
    grind
  ·
    split_ifs
    ·
      exfalso
      exact absurd (by assumption) (not_le.mpr h_stop_lt)
    ·
      convert mem_sliced_indices_neg_one h_stop_lt h_start_le x h_stop_le h_x_lt_start using 1
      grind


private lemma slice_range_neg_succ_mem
  {a b : ℤ}
  {step : ℕ}
-- given
  (h_stop_lt : (Add_Mul_DivSub1Sign_2 n b + 1).toNat < (Add_Mul_DivSub1Sign_2 n a + 1).toNat.min n)
  (h_start_le : (Add_Mul_DivSub1Sign_2 n a + 1).toNat.min n ≤ n)
  (x : Fin n)
  (h_mem : x ∈ Nat.sliced_indices' h_stop_lt h_start_le (Nat.succ_pos step)) :
-- imply
  x ∈ Slice.range ⟨a, b, Int.negSucc step⟩ n := by
-- proof
  simp only [Slice.range]
  split_ifs
  ·
    exact absurd (by assumption) (not_le.mpr h_stop_lt)
  ·
    exact h_mem


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Range.is.Mod.In_Range |
| comm | Set.Mod.In_Range.is.In_Range |
| mp | Set.Mod.In_Range.of.In_Range |
| mpr | Set.In_Range.of.Mod.In_Range |
-/
@[main, comm, mp, mpr]
private lemma main
  {n : ℕ}
  {a b d : ℤ}
-- given
  (x : Fin n) :
-- imply
  x ∈ Slice.range ⟨a, b, d⟩ n ↔ x ∈ Slice.range ⟨a, b, sign d⟩ n ∧ (x : ℤ) % d = (Slice.begin ⟨a, b, d⟩ n : ℤ) % d := by
-- proof
  constructor
  · intro h
    if hd₀ : d = 0 then
      subst hd₀
      simp [Slice.range] at h
    else if hd : 0 < d then
      have hsign := EqSign_1.of.Gt_0 hd
      match d, hd with
      | Int.ofNat (step + 1), _ =>
        simp only [Slice.range, Int.ofNat_eq_natCast] at h ⊢
        split_ifs at h
        · simp at h
        ·
          let start := (Add_Mul_DivSub1Sign_2 n a).toNat
          let stop := (Add_Mul_DivSub1Sign_2 n b).toNat.min n
          have h_stop_le : stop ≤ n := by grind
          obtain ⟨k, hk⟩ := mem_sliced_indices_pos (by grind) h_stop_le (Nat.succ_pos step) x h
          constructor
          ·
            rw [hsign]
            apply slice_range_step_one_mem (by grind) h_stop_le x _ (mem_sliced_indices_pos_lt_stop (by grind) h_stop_le (Nat.succ_pos step) x h)
            rw [hk]
            omega
          ·
            have h_norm : Slice.begin ⟨a, b, ↑(step + 1)⟩ n = start := by
              unfold Slice.begin
              simp [start]
            have h_x : (x : ℤ) = (start + k * step.succ : ℤ) := by
              push_cast
              exact_mod_cast hk
            rw [h_x, h_norm]
            apply int_add_mul_emod
      | Int.negSucc _, hd =>
        simp only [Slice.range] at h ⊢
        simp at hd
    else
      have hd' : d < 0 := lt_of_le_of_ne (not_lt.mp hd) (by rintro rfl; exact hd₀ rfl)
      have hsign := Sign.eq.Neg1.of.Lt_0 hd'
      match d, hd' with
      | Int.negSucc step, _ =>
        simp only [Slice.range, Int.negSucc_eq] at h ⊢
        split_ifs at h
        ·
          simp at h
        ·
          let start := (Add_Mul_DivSub1Sign_2 n a + 1).toNat.min n
          have h_stop_lt : (Add_Mul_DivSub1Sign_2 n b + 1).toNat < start := by grind
          have h_start_le : start ≤ n := by grind
          obtain ⟨k, hk⟩ := mem_sliced_indices_neg h_stop_lt h_start_le (Nat.succ_pos step) x h
          have h_stop_le := mem_sliced_indices_neg_ge_stop h_stop_lt h_start_le (Nat.succ_pos step) x h
          have h_x_lt_start := mem_sliced_indices_neg_lt_start h_stop_lt h_start_le (Nat.succ_pos step) x h
          have hk' : x.val = start - 1 - k * step.succ := by omega
          constructor
          ·
            rw [hsign]
            exact slice_range_sign_neg_one_mem h_stop_lt h_start_le x h_stop_le h_x_lt_start
          ·
            let m := start - 1
            have h_norm : Slice.begin ⟨a, b, (-[step+1])⟩ n = m := by
              dsimp [m, start]
              unfold Slice.begin
              simp
            have h_norm' : Slice.begin ⟨a, b, (-(↑step + 1))⟩ n = m := by
              rw [← Int.negSucc_eq, h_norm]
            have h_le : k * step.succ ≤ m := by omega
            have h_x_val : (x.val : ℤ) = (m : ℤ) + (k : ℤ) * (-[step+1]) := by
              rw [hk']
              rw [Nat.cast_sub h_le]
              simp [Int.negSucc_eq]
              ring
            have h_x : (x : ℤ) = (m : ℤ) + (k : ℤ) * (-[step+1]) := by simpa using h_x_val
            rw [h_x, h_norm']
            have h_d : (-[step+1] : ℤ) = -(↑step + 1) := by simp [Int.negSucc_eq]
            rw [h_d]
            apply int_add_mul_emod
      | Int.ofNat a, hd =>
        simp only [Slice.range] at h ⊢
        apply absurd hd (not_lt.mpr ?_)
        grind
  ·
    intro h
    obtain ⟨h_sign, h_mod⟩ := h
    if hd₀ : d = 0 then
      subst hd₀
      simp [Slice.range] at h_sign ⊢
    else if hd : 0 < d then
      have hsign := EqSign_1.of.Gt_0 hd
      match d, hd with
      | Int.ofNat (step + 1), _ =>
        rw [hsign] at h_sign
        simp only [Slice.range] at h_sign ⊢
        split_ifs at h_sign
        ·
          simp at h_sign
        ·
          let start := (Add_Mul_DivSub1Sign_2 n a).toNat
          let stop := (Add_Mul_DivSub1Sign_2 n b).toNat.min n
          have h_start_lt : start < stop := by grind
          have h_stop_le : stop ≤ n := by simp [stop]
          have h_norm : Slice.begin ⟨a, b, ↑(step + 1)⟩ n = start := by
            unfold Slice.begin
            simp [start]
          have h_mod_nat : x.val % step.succ = start % step.succ := by
            have h1 : (x.val : ℤ) % ↑(step + 1) = (start : ℤ) % ↑(step + 1) := by
              rw [← h_norm, Fin.val]
              exact h_mod
            exact_mod_cast h1
          obtain ⟨j, hj⟩ := mem_sliced_indices_pos h_start_lt h_stop_le Nat.one_pos x h_sign
          have h_x_lt_stop := mem_sliced_indices_pos_lt_stop h_start_lt h_stop_le Nat.one_pos x h_sign
          have hj_mod := nat_mod_eq_zero_of_add_mod_eq (Nat.succ_pos step) (by simpa [hj, Nat.one_mul] using h_mod_nat)
          obtain ⟨k, hk⟩ := exists_eq_mul_of_mod_eq_zero (Nat.succ_pos step) hj_mod
          have h_mem := mem_sliced_indices_pos_of_eq_add_mul h_start_lt h_stop_le (Nat.succ_pos step) x ⟨k, by rw [hj, hk, Nat.mul_comm, Nat.one_mul]⟩ h_x_lt_stop
          exact slice_range_step_succ_mem h_start_lt h_stop_le x h_mem
      | Int.negSucc _, hd =>
        simp at hd
    else
      have hd' : d < 0 := lt_of_le_of_ne (not_lt.mp hd) (by rintro rfl; exact hd₀ rfl)
      have hsign := Sign.eq.Neg1.of.Lt_0 hd'
      match d, hd' with
      | Int.negSucc step, _ =>
        have h_sign' : x ∈ Slice.range ⟨a, b, (-1 : ℤ)⟩ n := by simpa [hsign] using h_sign
        unfold Slice.range at h_sign'
        dsimp [Slice.step, Slice.mk] at h_sign'
        split at h_sign'
        ·
          rename_i step0 heq
          have : (0 : ℤ) ≤ Int.ofNat step0 := Int.natCast_nonneg step0
          linarith [heq]
        ·
          rename_i step0 heq
          have hstep0 : step0 = 0 := Int.negSucc.inj heq.symm
          split_ifs at h_sign'
          ·
            simp at h_sign'
          ·
            let start := (Add_Mul_DivSub1Sign_2 n a + 1).toNat.min n
            have h_stop_lt : (Add_Mul_DivSub1Sign_2 n b + 1).toNat < start := by
              dsimp [start]
              exact Nat.lt_of_not_le (by assumption)
            have h_start_le : start ≤ n := by simp [start]
            let m := start - 1
            have h_norm : Slice.begin ⟨a, b, (-[step+1])⟩ n = m := by
              dsimp [m, start]
              unfold Slice.begin
              simp
            have h_sign'' : x ∈ Nat.sliced_indices' h_stop_lt h_start_le Nat.one_pos := by simpa [hstep0] using h_sign'
            have h_stop_le := mem_sliced_indices_neg_ge_stop h_stop_lt h_start_le Nat.one_pos x h_sign''
            obtain ⟨j, hj⟩ := mem_sliced_indices_neg h_stop_lt h_start_le Nat.one_pos x h_sign''
            have hx_eq : x.val = m - j := by omega
            have hj_mod : j % step.succ = 0 := by
              have hj_le : j ≤ m := by omega
              have h1 : ((m : ℤ) - j) % (-[step+1]) = ((m : ℤ) % (-[step+1])) := by
                simpa [Int.natCast_sub hj_le, hx_eq, Fin.val, h_norm] using h_mod
              have h2 : ((m : ℤ) - (m - j : ℤ)) % (-[step+1]) = 0 := by
                rw [Int.sub_emod, h1, sub_self, Int.zero_emod]
              have h3 : (j : ℤ) % (-[step+1]) = 0 := by
                simpa [Int.natCast_sub, hx_eq] using h2
              have h_d : (-[step+1] : ℤ) = -(↑step + 1) := by simp [Int.negSucc_eq]
              rw [h_d, Int.emod_neg] at h3
              exact_mod_cast h3
            obtain ⟨k, hk⟩ := exists_eq_mul_of_mod_eq_zero (Nat.succ_pos step) hj_mod
            have h_mem := mem_sliced_indices_neg_of_eq h_stop_lt h_start_le (Nat.succ_pos step) x ⟨k, by rw [← hk, ← hj]; omega⟩ h_stop_le
            exact slice_range_neg_succ_mem h_stop_lt h_start_le x h_mem
      | Int.ofNat a, hd =>
        simp only [Slice.range] at h_sign ⊢
        apply absurd hd (not_lt.mpr ?_)
        grind


-- created on 2023-05-30
-- updated on 2026-09-02
