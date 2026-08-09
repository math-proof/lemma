import Lemma.Int.EqToNat
import Lemma.List.GetSlicedIndices.eq.AddMul.of.GtLength.Gt_0.Le.Lt
import Lemma.List.LengthRange.eq.Length
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import sympy.vector.vector
open Int Nat Slice List


@[main, comm]
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
  split_ifs with h_empty
  ·
    grind
  ·
    denote h_start_eq : start = (Add_Mul_DivSub1Sign_2 N a).toNat
    denote h_stop_eq : stop = (Add_Mul_DivSub1Sign_2 N b).toNat.min N
    simp only [← h_start_eq, GetElem.getElem, List.Vector.get]
    have h_start_lt : start < stop := by grind
    have h_stop_le : stop ≤ N := by simp [stop]
    have h_val := GetSlicedIndices.eq.AddMul.of.GtLength.Gt_0.Le.Lt
      h_start_lt
      h_stop_le
      (Nat.succ_pos step)
      (by simpa [Slice.length, h_start_eq, h_stop_eq, LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt (step := step + 1) h_start_lt h_stop_le (Nat.succ_pos step), EqAdd_Mul_DivSub1Sign_2, Nat.min_eq_left, EqToNat] using i.isLt)
    grind


-- created on 2026-08-07
