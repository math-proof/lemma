import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt_Length.Gt_0.Le.Lt
import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Int.EqToNat
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.EqMin
import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Nat.Gt_0
import Lemma.Nat.LeCoeS.is.Le
import Lemma.Nat.LtCoeS.is.Lt
import Lemma.Nat.LtVal
import Lemma.Nat.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Vector.EqLengthSlice.of.Lt
import sympy.core.relational
import sympy.vector.vector
open Bool Int Nat Vector List


@[main]
private lemma main
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  (List.Vector.indices ⟨j, m * n, n⟩ (m * n)).get ⟨i, by simp [EqLengthSlice.of.Lt m (LtVal j)]⟩ = ↑i * n + j := by
-- proof
  unfold List.Vector.indices Slice.toList
  simp
  have h_j := LtVal j
  have h_i := LtVal i
  have h_n := Gt_0 j
  have h_m := Gt_0 i
  split_ifs with h
  ·
    rw [MulCoeS.eq.CoeMul] at h
    repeat rw [EqAdd_Mul_DivSub1Sign_2] at h
    rw [EqToNat] at h
    rw [LeCoeS.is.Le] at h
    rw [Or.comm] at h
    rw [Or_Or.is.OrOr] at h
    simp at h
    contrapose! h
    constructor
    ·
      nlinarith
    ·
      apply Mul.gt.Zero.of.Gt_0.Gt_0
      repeat omega
  ·
    rw [MulCoeS.eq.CoeMul] at h
    repeat rw [EqAdd_Mul_DivSub1Sign_2] at h
    rw [EqToNat] at h
    rw [LeCoeS.is.Le] at h
    rw [Or.comm] at h
    rw [Or_Or.is.OrOr] at h
    simp at h
    match n with
    | 0 =>
      contradiction
    | n + 1 =>
      denote h_n' : n' = n + 1
      simp -- [← h_n']
      denote h_start_eq : start = (Slice.Add_Mul_DivSub1Sign_2 (m * (n + 1)) ↑↑j).toNat
      denote h_stop_eq : stop = (Slice.Add_Mul_DivSub1Sign_2 (m * (n + 1)) (↑m * (↑n + 1))).toNat.min (m * (n + 1))
      simp [← h_start_eq, ← h_stop_eq]
      rw [EqAdd_Mul_DivSub1Sign_2, EqToNat] at h_start_eq
      rw [OfNat.eq.Cast (α := ℤ), AddCoeS.eq.CoeAdd, MulCoeS.eq.CoeMul, EqAdd_Mul_DivSub1Sign_2, EqToNat] at h_stop_eq
      simp at h_stop_eq
      denote h_step_eq : step = n.succ
      let ⟨h_lt, h_pos⟩ := h
      have h_start : start < stop := by simpa [h_start_eq, h_stop_eq]
      have h_stop : stop ≤ m * (n + 1) := by simp [stop]
      have h_step : step > 0 := by simp [step]
      simp [h_start_eq, h_stop_eq]
      have := GetSlicedIndices.eq.AddMul.of.Lt_Length.Gt_0.Le.Lt h_lt (by simp) (by simp) (j := j) (m := m) (n := n + 1) (i := i)
        (by
          rw [List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt]
          simp
          sorry
        )
      sorry


-- created on 2025-11-07
-- updated on 2025-11-08
