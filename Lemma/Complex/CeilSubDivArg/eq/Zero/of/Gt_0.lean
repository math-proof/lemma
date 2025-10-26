import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Set.InDiv.of.In_Ioc.Gt_0
import Lemma.Set.InSub.of.In_Ioc
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.Div_Mul.eq.Inv.of.Ne_0
import Lemma.Rat.DivNeg.eq.NegDiv
import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.DivDiv.eq.Div_Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul
import Lemma.Real.Pi.gt.Zero
import Lemma.Nat.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Real.Pi.ne.Zero
import Lemma.Set.EqCeil_0.of.In_Ioc
import Lemma.Set.In.of.In.Subset
import Lemma.Set.SubsetIocS.of.Le.Ge
import Lemma.Int.Le_Sub.is.LeAdd
import Lemma.Nat.LeInv_1.of.Gt_0
import Lemma.Int.Ge_Sub.of.GeAdd
import Lemma.Nat.GtCoe_0.is.Gt_0
open Set Complex Rat Nat Int Real


@[main]
private lemma main
  {z : ℂ}
  {n : ℕ}
-- given
  (h : n > 0) :
-- imply
  ⌈arg z / (2 * n * Real.pi) - 1 / 2⌉ = 0 := by
-- proof
  have h_mem := Arg.in.IocNegPiPi z
  have h_mem := InDiv.of.In_Ioc.Gt_0 h_mem (by apply GtCoe_0.of.Gt_0 h : (n : ℝ) > 0)
  have h_mem := InSub.of.In_Ioc h_mem Real.pi
  have h_Gt_0 := Mul.gt.Zero.of.Gt_0.Gt_0 (by norm_num : (2 : ℝ) > 0) Pi.gt.Zero
  have h_mem := InDiv.of.In_Ioc.Gt_0 h_mem h_Gt_0
  simp only [DivSub.eq.SubDivS] at h_mem
  simp only [DivDiv.eq.Div_Mul] at h_mem
  rw [DivNeg.eq.NegDiv] at h_mem
  simp only [Mul_Mul.eq.MulMul] at h_mem
  simp only [Div_Mul.eq.Inv.of.Ne_0 Pi.ne.Zero true] at h_mem
  simp only [Inv.eq.Div1] at h_mem
  simp only [Mul.comm (b := (2 : ℝ))] at h_mem
  apply EqCeil_0.of.In_Ioc
  apply In.of.In.Subset _ h_mem
  have := LeInv_1.of.Gt_0 h
  apply SubsetIocS.of.Le.Ge
  ·
    apply Le_Sub.of.LeAdd
    norm_num
    assumption
  ·
    apply Ge_Sub.of.GeAdd
    norm_num
    assumption


-- created on 2025-03-02
-- updated on 2025-08-02
