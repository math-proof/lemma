import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Int.Le_Sub.is.LeAdd
import Lemma.Nat.GtCoe_0.is.Gt_0
import Lemma.Nat.LeInv_1.of.Gt_0
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.DivDiv.eq.Div_Mul
import Lemma.Rat.DivNeg.eq.NegDiv
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.Div_Mul.eq.Inv.of.Ne_0
import Lemma.Real.GtPi0
import Lemma.Real.NePi0
import Lemma.Set.EqCeil_0.of.In_Ioc
import Lemma.Set.In.of.In.Subset
import Lemma.Set.InDiv.of.In_Ioc.Gt_0
import Lemma.Set.InSub.of.In_Ioc
import Lemma.Set.SubsetIocS.of.Le.Ge
import Lemma.Int.LeSub.is.Le_Add
open Complex Int Nat Rat Real Set


@[main]
private lemma main
-- given
  (z : ℂ)
  (n : ℕ) :
-- imply
  ⌈arg z / (2 * n * π) - 1 / 2⌉ = 0 := by
-- proof
  if h_n : n = 0 then
    subst h_n
    norm_num
  else
    have h_mem := Arg.in.IocNegPiPi z
    have h_n : n > 0 := by omega
    have h_mem := InDiv.of.In_Ioc.Gt_0 h_mem (GtCoe_0.of.Gt_0 h_n)
    have h_mem := InSub.of.In_Ioc h_mem π
    have h_pos := Lt0Mul.of.Gt_0.Gt_0 (by norm_num : (2 : ℝ) > 0) GtPi0
    have h_mem := InDiv.of.In_Ioc.Gt_0 h_mem h_pos
    simp only [DivSub.eq.SubDivS] at h_mem
    simp only [DivDiv.eq.Div_Mul] at h_mem
    rw [DivNeg.eq.NegDiv] at h_mem
    simp only [Mul_Mul.eq.MulMul] at h_mem
    simp only [Div_Mul.eq.Inv.of.Ne_0 NePi0 true] at h_mem
    simp only [Inv.eq.Div1] at h_mem
    simp only [Mul.comm (b := (2 : ℝ))] at h_mem
    apply EqCeil_0.of.In_Ioc
    apply In.of.In.Subset _ h_mem
    have := LeInv_1.of.Gt_0 h_n
    apply SubsetIocS.of.Le.Ge
    ·
      apply Le_Sub.of.LeAdd
      norm_num
      assumption
    ·
      apply Ge_Sub.of.GeAdd
      norm_num
      assumption


-- created on 2018-11-05
-- updated on 2026-08-03
