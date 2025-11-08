import sympy.core.relational
import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Int.EqToNat
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Nat.Gt_0
import Lemma.Nat.LeCoeS.is.Le
import Lemma.Nat.LtVal
import Lemma.Nat.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Vector.EqLengthSlice.of.Lt
import sympy.vector.vector
open Bool Int Nat Vector


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
      -- simp [← h_n']
      -- apply Eq_Mk.of.EqVal
      sorry

@[main]
private lemma test
-- given
  (j : Fin n) :
-- imply
  j < n := by
-- proof
  match n with
  | 0 =>
    have h := j.isLt
    aesop
  | n + 1 =>
    -- let n' := n + 1
    -- have h_n' : n' = n + 1 := rfl
    -- simplified to:
    denote h_n' : n' = n + 1
    simp

-- created on 2025-11-07
