import Lemma.Int.EqToNat
import Lemma.List.GetSlicedIndices.eq.AddMul.of.GtLength.Gt_0.Le.Lt
import Lemma.List.LengthSlice.eq.Zero
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.Add_Mul.eq.Add_MulAddDiv
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Mul.lt.MulToNatCeilDivSub.of.GtSub.Gt_0.Lt
import Lemma.Rat.EqToNatCeil_0.of.Le
import Lemma.Vector.GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
import Lemma.Vector.GtMin.of.GtLengthSlice
import Lemma.Vector.LtGetSlicedIndices.of.GtLength.Gt_0.Le.Lt
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SEq.of.Eq_0.Eq_0
open Int List Nat Rat Vector Slice


@[main]
private lemma main
  {a b d n : ℕ}
-- given
  (h_d : d > 0)
  (i : Fin ((⟨a, b, d⟩ : Slice).length n)) :
-- imply
  a / d + i < (⟨(a % d : ℕ), (n : ℕ), (d : ℕ)⟩ : Slice).length n := by
-- proof
  set stop := b ⊓ n with hstop
  have hi := i.isLt
  unfold Slice.length at hi
  simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat] at hi
  rcases le_or_gt ⌈((stop : ℚ) - a) / d⌉.toNat 0 with hL0 | hLpos
  ·
    have h_len_zero : (⟨a, b, d⟩ : Slice).length n = 0 := by
      unfold Slice.length
      simp only [hstop, EqAdd_Mul_DivSub1Sign_2, EqToNat, Nat.le_zero_eq] at hL0 ⊢
      exact hL0
    grind
  ·
    have hLpos' : (⟨a, b, d⟩ : Slice).length n > 0 := by
      unfold Slice.length
      simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat]
      exact Nat.pos_of_ne_zero (Nat.ne_of_gt hLpos)
    have h_start_lt := GtMin.of.GtLengthSlice hLpos'
    have h_stop_le := Nat.min_le_right b n
    have h_inner_lt : a % d + (a / d + i) * d < n := calc
      _ = a + i * d := Add_MulAddDiv.eq.Add_Mul a d i
      _ < stop := by
        rw [AddMul.eq.GetSlicedIndices.of.GtLength.Gt_0.Le.Lt h_start_lt h_stop_le h_d]
        apply LtGetSlicedIndices.of.GtLength.Gt_0.Le.Lt h_start_lt h_stop_le h_d
        simpa [Slice.length, hstop, EqAdd_Mul_DivSub1Sign_2, EqToNat, LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt (start := a) (stop := stop) (n := n) h_start_lt h_stop_le h_d] using hi
      _ ≤ n := h_stop_le
    unfold Slice.length
    simp only [Nat.min_eq_right (Nat.le_refl n), EqAdd_Mul_DivSub1Sign_2, EqToNat]
    apply Nat.lt_of_mul_lt_mul_left
    rw [Nat.mul_comm d ⌈((n : ℚ) - ↑(a % d)) / d⌉.toNat]
    simpa [Nat.mul_comm] using Mul.lt.MulToNatCeilDivSub.of.GtSub.Gt_0.Lt (Nat.lt_of_le_of_lt (Nat.mod_le a d) (Nat.lt_of_lt_of_le h_start_lt h_stop_le)) h_d (lt_sub_of_add_lt (by simpa [Nat.add_comm] using h_inner_lt))


-- created on 2026-08-09
