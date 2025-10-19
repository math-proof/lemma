import Lemma.Nat.Le_Sub_1
import Lemma.Nat.LeMulS.of.Le.Ge_0
import Lemma.Algebra.LeAddS.of.Le.Le
import Lemma.Algebra.Lt.of.Le_Sub_1.Gt_0
import Lemma.Nat.MulSub.eq.SubMulS
import Lemma.Int.SubAdd.eq.Add_Sub
import Lemma.Nat.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
open Algebra Nat Int


@[main]
private lemma main
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


-- created on 2025-05-07
-- updated on 2025-05-09
