import Lemma.Int.EqToNat
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Rat.LeToNatCeil_1.of.Ge_Sub
import sympy.vector.vector
open Int List Nat Rat Slice


private lemma get_sliced_indices_sub
  {start stop N d i : ℕ}
-- given
  (h_d : d > 0)
  (h_gt : start > stop)
  (h_start_le : start ≤ N)
  (h_i : i < (Nat.sliced_indices' h_gt h_start_le h_d).length) :
-- imply
  (Nat.sliced_indices' h_gt h_start_le h_d)[i] = start - 1 - i * d := by
-- proof
  induction i generalizing start stop with
  | zero =>
    unfold Nat.sliced_indices'
    obtain h | h := lt_or_ge (stop + d) start
    · simp
    · simp
  | succ i ih =>
    obtain h | h := lt_or_ge (stop + d) start
    ·
      have h_tail : start - d > stop := by omega
      have h_gt' : start - d > stop := h_tail
      have h_start' : start - d ≤ N := by omega
      have h_len :
          (Nat.sliced_indices' h_gt h_start_le h_d).length =
            (Nat.sliced_indices' h_gt' h_start' h_d).length + 1 := by
        conv_lhs =>
          unfold Nat.sliced_indices'
          simp only [h_tail, dite_true, List.length_cons]
      have ih' := ih (start := start - d) (stop := stop) h_gt' h_start' (by omega)
      conv_lhs =>
        unfold Nat.sliced_indices'
        simp only [h_tail, dite_true, List.get_cons_succ]
      simp [ih', Nat.sub_sub]
      ring_nf
    ·
      have h_len_le : (Nat.sliced_indices' h_gt h_start_le h_d).length ≤ 1 := by
        rw [LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt
          (start := start) (stop := stop) (n := N) h_gt h_start_le h_d]
        apply LeToNatCeil_1.of.Ge_Sub (by omega)
      apply absurd (Nat.succ_le_of_lt h_i) (Nat.not_le_of_gt (by omega))


@[main]
private lemma main
  {a b : ℤ}
  {N d : ℕ}
-- given
  (h_d : d > 0)
  (i : Fin _) :
-- imply
  ↑(List.Vector.indices ⟨a, b, -(d : ℤ)⟩ N)[i] =
    (Add_Mul_DivSub1Sign_2 N a + 1).toNat.min N - 1 - d * ↑i := by
-- proof
  match d with
  | 0 => exact absurd h_d (Nat.lt_irrefl 0)
  | Nat.succ step =>
    have h_neg : -(Nat.succ step : ℤ) = Int.negSucc step := by
      push_cast
      rw [← Int.negSucc_eq]
    have h_slice : (⟨a, b, -(Nat.succ step : ℤ)⟩ : Slice) = ⟨a, b, Int.negSucc step⟩ := by
      rw [Slice.mk.injEq]
      exact ⟨rfl, rfl, h_neg⟩
    have h_len :
        ((⟨a, b, -(Nat.succ step : ℤ)⟩ : Slice).length N) =
          ((⟨a, b, Int.negSucc step⟩ : Slice).length N) := by
      rw [h_slice]
    let i' : Fin ((⟨a, b, Int.negSucc step⟩ : Slice).length N) := Fin.cast h_len.symm i
    have h_main :
        ↑(List.Vector.indices ⟨a, b, Int.negSucc step⟩ N)[i'] =
          (Add_Mul_DivSub1Sign_2 N a + 1).toNat.min N - 1 - (step + 1) * ↑i' := by
      unfold List.Vector.indices Slice.range
      simp
      have hi := i'.isLt
      split_ifs with h_empty
      ·
        have h_nil : (⟨a, b, Int.negSucc step⟩ : Slice).range N = [] := by
          unfold Slice.range
          grind
        have h_len_zero : ((⟨a, b, Int.negSucc step⟩ : Slice).length N) = 0 := by
          rw [← LengthRange.eq.Length (s := ⟨a, b, Int.negSucc step⟩) (n := N), h_nil, List.length_nil]
        rw [h_len_zero] at i'
        exact i'.elim0
      ·
        denote h_start_eq : start = (Add_Mul_DivSub1Sign_2 N a + 1).toNat.min N
        denote h_stop_eq : stop = (Add_Mul_DivSub1Sign_2 N b + 1).toNat
        simp only [← h_start_eq, GetElem.getElem, List.Vector.get]
        have h_gt : start > stop := by grind
        have h_start_le : start ≤ N := by simp [h_start_eq]
        have h_val := get_sliced_indices_sub
          (i := i')
          (Nat.succ_pos step)
          h_gt
          h_start_le
          (by
            unfold Slice.length at hi
            simpa [h_start_eq, h_stop_eq,
              LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt
                (start := start) (stop := stop) (n := N) h_gt h_start_le (Nat.succ_pos step),
              EqAdd_Mul_DivSub1Sign_2, Nat.min_eq_left, EqToNat] using hi)
        convert h_val using 1
        · rfl
        · simp [Nat.mul_comm]
    have h_get_val :
        (List.Vector.indices ⟨a, b, -(Nat.succ step : ℤ)⟩ N)[i] =
          (List.Vector.indices ⟨a, b, Int.negSucc step⟩ N)[i'] := by
      dsimp [i']
      rcases h_slice with ⟨⟩
      rfl
    calc
      ↑(List.Vector.indices ⟨a, b, -(Nat.succ step : ℤ)⟩ N)[i]
          = ↑(List.Vector.indices ⟨a, b, Int.negSucc step⟩ N)[i'] := congrArg Fin.val h_get_val
      _ = (Add_Mul_DivSub1Sign_2 N a + 1).toNat.min N - 1 - (step + 1) * ↑i' := h_main
      _ = (Add_Mul_DivSub1Sign_2 N a + 1).toNat.min N - 1 - Nat.succ step * ↑i := by
        simp [i', Nat.succ_eq_add_one]


-- created on 2026-08-07
