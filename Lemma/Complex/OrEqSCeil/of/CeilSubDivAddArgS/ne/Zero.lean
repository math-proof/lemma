import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Set.Add.in.Ioc.of.In.In
import Lemma.Set.InDiv.of.In_Ioc.Gt_0
import Lemma.Set.InSub.of.In_Ioc
import Lemma.Set.In_Ico.Ceil.of.In_Icc
open Set Complex


@[main]
private lemma main
  {A B : ℂ}
-- given
  (h : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ ≠ 0) :
-- imply
  ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 1 ∨
    ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = -1 := by
-- proof
  have hA := Arg.in.IocNegPiPi A
  have hB := Arg.in.IocNegPiPi B
  have hsum := Add.in.Ioc.of.In.In hA hB
  have hπ : (2 * π : ℝ) > 0 := mul_pos two_pos Real.pi_pos
  have hdiv := InDiv.of.In_Ioc.Gt_0 hsum hπ
  have hsub := InSub.of.In_Ioc hdiv (1 / 2)
  have h0 : (-π + -π) / (2 * π) - 1 / 2 = (-3 / 2 : ℝ) := by
    field_simp
    ring
  have h1 : (π + π) / (2 * π) - 1 / 2 = (1 / 2 : ℝ) := by
    field_simp
    ring
  rw [h0, h1] at hsub
  have hceil := In_Ico.Ceil.of.In_Icc hsub
  have hf : ⌊((-3 / 2 : ℝ))⌋ = -2 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num
  have hc : ⌈(1 / 2 : ℝ)⌉ = 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor <;> norm_num
  rw [hf, hc] at hceil
  rcases hceil with ⟨hlo, hhi⟩
  omega


-- created on 2018-10-24
-- updated on 2026-08-20
