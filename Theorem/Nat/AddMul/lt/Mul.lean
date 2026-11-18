module

public import Theorem.Nat.Le_Sub_1
public import Theorem.Nat.LeMulS.of.Le.Ge_0
public import Theorem.Nat.LeAddS.of.Le.Le
public import Theorem.Nat.Lt.of.Le_Sub_1.Gt_0
public import Theorem.Nat.MulSub.eq.SubMulS
public import Theorem.Int.SubAdd.eq.Add_Sub
public import Theorem.Nat.SubAdd.eq.Add_Sub.of.Ge
public import Theorem.Nat.EqAddSub.of.Ge
public import Theorem.Nat.Mul

public section

open Nat Int


public theorem Nat.AddMul.lt.Mul
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  i * n + j < m * n := by
-- proof
  have hi := Le_Sub_1 i
  have hin := LeMulS.of.Le.Ge_0 hi (show n ≥ 0 by simp)
  have hj := Le_Sub_1 j
  have h_Le := LeAddS.of.Le.Le hin hj
  rw [MulSub.eq.SubMulS] at h_Le
  simp at h_Le
  have hi : i < m := by simp
  have hm : m > 0 := by linarith
  have hj : j < n := by simp
  have hn : n > 0 := by linarith
  rw [Add_Sub.eq.SubAdd.of.Ge (by linarith)] at h_Le
  rw [EqAddSub.of.Ge (by nlinarith)] at h_Le
  apply Lt.of.Le_Sub_1.Gt_0 (by nlinarith)
  assumption


public theorem Nat.AddMul.lt.Mul.comm
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  i * n + j < n * m := by
-- proof
  have := AddMul.lt.Mul i j
  conv_rhs at this => rw [Nat.mul_comm]
  assumption


-- created on 2025-05-07
-- updated on 2025-05-09
