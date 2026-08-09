import Lemma.List.LengthSlice.eq.Zero
import Lemma.Int.EqToNat
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Rat.Div.le.Zero.of.Le_0
import Lemma.Rat.LeToNatCeil_1.of.Le_Add
import Lemma.Vector.GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
import Lemma.Vector.GetSlice.eq.MapRange
import Lemma.Vector.EqGetRange
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SEq.of.Eq_0.Eq_0
open List Vector Int Nat Rat Slice


private lemma get_sliced_indices_add
  {start stop N d i : ℕ}
  (h_d : d > 0)
  (h_start_lt : start < stop)
  (h_stop_le : stop ≤ N)
  (h_i : i < (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length) :
  (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d)[i] = start + i * d := by
  induction i generalizing start stop with
  | zero =>
    unfold Nat.sliced_indices
    grind
  | succ i ih =>
    obtain h_start' | h := lt_or_ge (start + d) stop
    ·
      conv_lhs =>
        unfold Nat.sliced_indices
        simp only [h_start', dite_true, List.get_cons_succ]
      erw [ih h_start' h_stop_le]
      ring_nf
    ·
      apply absurd (Nat.succ_le_of_lt h_i) (Nat.not_le_of_gt ?_)
      simp
      rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start_lt h_stop_le h_d]
      apply (LeToNatCeil_1.of.Le_Add h (α := ℚ)).trans
      omega


private lemma sliced_get_lt_stop
  {start stop N d : ℕ}
  (h_d : d > 0)
  (h_start_lt : start < stop)
  (h_stop_le : stop ≤ N)
  {i : ℕ}
  (h_i :
    i <
      (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length) :
  (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d)[i].val < stop := by
  induction i generalizing start stop with
  | zero =>
    unfold Nat.sliced_indices
    obtain h | h := lt_or_ge (start + d) stop
    · simp [h, h_start_lt]
    · simp [h_start_lt]
  | succ i ih =>
    obtain h | h := lt_or_ge (start + d) stop
    ·
      have h_start' : start + d < stop := h
      have h_len :
          (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length =
            (Nat.sliced_indices (step := d) h_start' h_stop_le h_d).length + 1 := by
        conv_lhs =>
          unfold Nat.sliced_indices
          simp only [h, dite_true, List.length_cons]
      have hi_tail :
          i <
            (Nat.sliced_indices (step := d) h_start' h_stop_le h_d).length := by
        omega
      have ih_tail := ih h_start' h_stop_le hi_tail
      conv_lhs =>
        unfold Nat.sliced_indices
        simp only [h, dite_true, List.get_cons_succ]
      have h_succ := get_sliced_indices_add h_d h_start' h_stop_le hi_tail
      simpa [h_succ] using ih_tail
    ·
      have h_len_le :
          (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length ≤ 1 := by
        rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
          (start := start) (stop := stop) (n := N) h_start_lt h_stop_le h_d]
        apply LeToNatCeil_1.of.Le_Add h
      exact absurd (Nat.succ_le_of_lt h_i) (Nat.not_le_of_gt (by omega))


private lemma outer_start_lt_stop
  (a b d n : ℕ)
  (hLpos : (⟨a, b, d⟩ : Slice).length n > 0) :
  a < min b n := by
  set stop := min b n with hstop
  by_contra h
  push_neg at h
  have h_ge : stop ≤ a := h
  have h_toNat : ⌈((stop : ℚ) - a) / d⌉.toNat = 0 := by
    have h_le : (stop : ℚ) - a ≤ 0 := sub_nonpos.mpr (Nat.cast_le.mpr h_ge)
    have h_ceil_le : ⌈((stop : ℚ) - a) / d⌉ ≤ 0 := by
      apply Int.ceil_nonpos.mpr
      simpa using Div.le.Zero.of.Le_0 h_le d
    omega
  have h_len_zero : (⟨a, b, d⟩ : Slice).length n = 0 := by
    unfold Slice.length
    simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat]
    grind
  rw [h_len_zero] at hLpos
  exact Nat.lt_irrefl 0 hLpos


private lemma inner_index_lt
  (a b d n : ℕ)
  (h_d : d > 0)
  (i : Fin ((⟨a, b, d⟩ : Slice).length n)) :
  a / d + i.val < (⟨a % d, n, d⟩ : Slice).length n := by
  set stop := min b n with hstop
  have hi := i.isLt
  unfold Slice.length at hi ⊢
  simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat] at hi ⊢
  rcases le_or_gt ⌈((stop : ℚ) - a) / d⌉.toNat 0 with hL0 | hLpos
  ·
    have h_len_zero : (⟨a, b, d⟩ : Slice).length n = 0 := by
      unfold Slice.length
      simp only [hstop, EqAdd_Mul_DivSub1Sign_2, EqToNat, Nat.le_zero_eq] at hL0 ⊢
      exact hL0
    rw [h_len_zero] at i
    exact i.elim0
  ·
    have hLpos' : (⟨a, b, d⟩ : Slice).length n > 0 := by
      unfold Slice.length
      simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat]
      exact Nat.pos_of_ne_zero (Nat.ne_of_gt hLpos)
    have h_start_lt : a < stop := outer_start_lt_stop a b d n hLpos'
    have h_stop_le : stop ≤ n := Nat.min_le_right b n
    have h_len :=
      LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
        (start := a) (stop := stop) (n := n) h_start_lt h_stop_le h_d
    have hi' :
        i.val <
          (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length := by
      simpa [Slice.length, hstop, EqAdd_Mul_DivSub1Sign_2, EqToNat, h_len] using hi
    have h_fin_lt := sliced_get_lt_stop h_d h_start_lt h_stop_le hi'
    have h_val := get_sliced_indices_add h_d h_start_lt h_stop_le hi'
    have h_outer_lt : a + i.val * d < stop := by
      rw [← h_val]
      exact h_fin_lt
    simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat]
    have h_inner_lt : a % d + (a / d + i.val) * d < n := by
      calc
        a % d + (a / d + i.val) * d = a / d * d + i.val * d + a % d := by ring
        _ = a + i.val * d := by
          have := Nat.mod_add_div a d
          omega
        _ < stop := h_outer_lt
        _ ≤ n := h_stop_le
    have h_mul : (a / d + i.val) * d < n - a % d := by
      have := h_inner_lt
      omega
    exact (Nat.div_lt_iff_lt_mul h_d).mpr h_mul


private lemma inner_slice_length
  (a b d n : ℕ)
  (h_d : d > 0) :
  (⟨a / d, a / d + (⟨a, b, d⟩ : Slice).length n, 1⟩ : Slice).length
      ((⟨a % d, n, d⟩ : Slice).length n) =
    (⟨a, b, d⟩ : Slice).length n := by
  set L := (⟨a, b, d⟩ : Slice).length n with hL
  set len_g := (⟨a % d, n, d⟩ : Slice).length n with hlen_g
  unfold Slice.length
  simp only [hL, hlen_g]
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  ·
    omega
  ·
    have h_upper : a / d + L ≤ len_g := by
      have := inner_index_lt a b d n h_d ⟨L - 1, Nat.sub_one_lt_of_lt hLpos⟩
      simp at this
      omega
    have h_min : min (a / d + L) len_g = a / d + L := Nat.min_eq_left h_upper
    simp
    omega


@[main]
private lemma main
-- given
  (f : List.Vector α n)
  (a b d : ℕ) :
-- imply
  f[a:b:d] ≃ f[a % d :n: d][a / d : a / d + (⟨a, b, d⟩ : Slice).length n] := by
-- proof
  if h_d : d = 0 then
    subst h_d
    apply SEq.of.Eq_0.Eq_0
    ·
      apply List.LengthSlice.eq.Zero
    ·
      simp [Slice.length]
  else
    have h_d : d > 0 := Nat.pos_of_ne_zero h_d
    set L := (⟨a, b, d⟩ : Slice).length n with hL
    set len_g := (⟨a % d, n, d⟩ : Slice).length n with hlen_g
    apply SEq.of.All_EqGetS.Eq
    · intro i
      have h_idx_lt := inner_index_lt a b d n h_d i
      have h_len_eq := inner_slice_length a b d n h_d
      simp only [GetElem.getElem, List.Vector.getSlice, List.Vector.get]
      congr 1
      · exact Fin.eq_of_val_eq <|
          calc
            _ = (Add_Mul_DivSub1Sign_2 n (a % d)).toNat + d * (a / d + i.val) := by
              simpa using GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0 (N := n) (a := a % d) (b := n) (d := d) h_d ⟨a / d + i.val, h_idx_lt⟩
            _ = (a / d + i.val) * d + a % d := by
              simp [Nat.mul_comm, Nat.add_comm]
              grind
            _ = a + i.val * d := by
              calc
                (a / d + i.val) * d + a % d = a / d * d + i.val * d + a % d := by ring
                _ = a + i.val * d := by
                  have := Nat.mod_add_div a d
                  omega
            _ = (Add_Mul_DivSub1Sign_2 n a).toNat + d * ↑i := by
              simpa [EqAdd_Mul_DivSub1Sign_2, EqToNat, Nat.mul_comm] using GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0 (N := n) (a := a) (b := b) (d := d) h_d i
            _ = ↑(List.Vector.indices ⟨a, b, d⟩ n)[i] := by
              simp [EqAdd_Mul_DivSub1Sign_2, EqToNat, Nat.mul_comm]
      · exact Fin.eq_of_val_eq <|
          calc
            ↑(List.Vector.indices ⟨a / d, a / d + L, 1⟩ len_g)[Fin.cast (by rw [← h_len_eq, hL]) i] =
                (Add_Mul_DivSub1Sign_2 len_g (a / d)).toNat + (a / d + i.val) := by
              simpa using
                GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
                  (N := len_g) (a := a / d) (b := a / d + L) (d := 1) Nat.one_pos
                  (Fin.cast (by rw [← h_len_eq, hL]) i)
            _ = a / d + i.val := by
              simp [EqAdd_Mul_DivSub1Sign_2, EqToNat, Nat.one_mul, Nat.add_comm]
    · exact (inner_slice_length a b d n h_d).symm


-- created on 2026-08-07
