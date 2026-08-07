import Lemma.Int.EqToNat
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Rat.LeToNatCeil_1.of.Le_Add
import sympy.vector.vector
open Int Nat Rat Slice


private lemma get_sliced_indices_add
  {start stop N d i : ℕ}
-- given
  (h_d : d > 0)
  (h_start_lt : start < stop)
  (h_stop_le : stop ≤ N)
  (h_i : i < (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length) :
-- imply
  (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d)[i] = start + i * d := by
-- proof
  induction i generalizing start stop with
  | zero =>
    unfold Nat.sliced_indices
    obtain h | h := lt_or_ge (start + d) stop
    · simp [h]
    · simp
  | succ i ih =>
    obtain h | h := lt_or_ge (start + d) stop
    ·
      have h_start' : start + d < stop := h
      have h_len : (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length = (Nat.sliced_indices (step := d) h_start' h_stop_le h_d).length + 1 := by
        conv_lhs =>
          unfold Nat.sliced_indices
          simp only [h, dite_true, List.length_cons]
      have ih' := ih h_start' h_stop_le (by omega)
      conv_lhs =>
        unfold Nat.sliced_indices
        simp only [h, dite_true, List.get_cons_succ]
      simp [ih']
      ring_nf
    ·
      have h_len_le : (Nat.sliced_indices (step := d) h_start_lt h_stop_le h_d).length ≤ 1 := by
        rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt (step := d) h_start_lt h_stop_le h_d]
        apply LeToNatCeil_1.of.Le_Add h
      apply absurd (Nat.succ_le_of_lt h_i) (Nat.not_le_of_gt (by omega))


@[main]
private lemma main
  {a b : ℤ}
  {N d : ℕ}
-- given
  (h_d : d > 0)
  (i : Fin _) :
-- imply
  ↑(List.Vector.indices ⟨a, b, d⟩ N)[i] = (Add_Mul_DivSub1Sign_2 N a).toNat + d * ↑i := by
-- proof
  obtain ⟨step, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_d)
  subst hd
  unfold List.Vector.indices Slice.range
  simp
  have hi := i.isLt
  split_ifs with h_empty
  ·
    have h_nil : (⟨a, b, ↑(step + 1)⟩ : Slice).range N = [] := by
      unfold Slice.range
      grind
    have h_len : (⟨a, b, ↑(step + 1)⟩ : Slice).length N = 0 := by
      rw [← LengthRange.eq.Length (s := ⟨a, b, ↑(step + 1)⟩) (n := N), h_nil, List.length_nil]
    rw [h_len] at i
    exact i.elim0
  ·
    denote h_start_eq : start = (Add_Mul_DivSub1Sign_2 N a).toNat
    denote h_stop_eq : stop = (Add_Mul_DivSub1Sign_2 N b).toNat.min N
    simp only [← h_start_eq, GetElem.getElem, List.Vector.get]
    have h_start_lt : start < stop := by grind
    have h_stop_le : stop ≤ N := by simp [stop]
    have h_val := get_sliced_indices_add
      (i := i)
      (Nat.succ_pos step)
      h_start_lt
      h_stop_le
      (by simpa [Slice.length, h_start_eq, h_stop_eq, LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt (step := step + 1) h_start_lt h_stop_le (Nat.succ_pos step), EqAdd_Mul_DivSub1Sign_2, Nat.min_eq_left, EqToNat] using hi)
    convert h_val using 1
    · rfl
    · simp [Nat.mul_succ, Nat.mul_comm]


-- created on 2026-08-07
