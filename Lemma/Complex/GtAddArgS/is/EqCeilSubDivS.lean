import sympy.core.numbers
import sympy.functions.elementary.complexes
import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Set.Add.in.Ioc.of.In.In
import Lemma.Set.InDiv.of.In_Ioc.Gt_0
import Lemma.Set.InSub.of.In_Ioc
import Lemma.Set.In_Ico.Ceil.of.In_Icc
import Lemma.Int.Gt_0.of.Lt0Ceil
open Set Complex Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.GtAddArgS.is.EqCeilSubDivS |
| comm | Complex.EqCeilSubDivS.is.GtAddArgS |
| mp | Complex.EqCeilSubDivS.of.GtAddArgS |
| mpr | Complex.GtAddArgS.of.EqCeilSubDivS |
-/
@[main, comm, mp, mpr]
private lemma main
  {A B : ℂ} :
-- imply
  arg A + arg B > π ↔ ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 1 := by
-- proof
  constructor
  ·
    intro h
    have hA := Arg.in.IocNegPiPi A
    have hB := Arg.in.IocNegPiPi B
    have hsum := Add.in.Ioc.of.In.In hA hB
    have hmem : arg A + arg B ∈ Ioc π (2 * π) := by
      constructor
      ·
        exact h
      ·
        have h2 : π + π = (2 * π : ℝ) := by ring
        rw [← h2]
        exact hsum.2
    have hπ : (2 * π : ℝ) > 0 := mul_pos two_pos Real.pi_pos
    have hdiv := InDiv.of.In_Ioc.Gt_0 hmem hπ
    have hsub := InSub.of.In_Ioc hdiv (1 / 2)
    have h0 : π / (2 * π) - 1 / 2 = (0 : ℝ) := by
      field_simp
      ring
    have h1 : (2 * π) / (2 * π) - 1 / 2 = (1 / 2 : ℝ) := by
      field_simp
      ring
    rw [h0, h1] at hsub
    have hceil := In_Ico.Ceil.of.In_Icc hsub
    have hf : ⌊(0 : ℝ)⌋ = 0 := Int.floor_zero
    have hc : ⌈(1 / 2 : ℝ)⌉ = 1 := by
      apply Int.ceil_eq_iff.mpr
      constructor <;> norm_num
    rw [hf, hc] at hceil
    rcases hceil with ⟨hlo, hhi⟩
    omega
  ·
    intro h
    have h_ceil : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ > 0 := by
      rw [h]
      norm_num
    have h_pos : (arg A + arg B) / (2 * π) - 1 / 2 > 0 :=
      Gt_0.of.Lt0Ceil h_ceil
    have hπ : 0 < 2 * π := mul_pos two_pos Real.pi_pos
    have h_div : 1 / 2 < (arg A + arg B) / (2 * π) := sub_pos.mp h_pos
    have := (lt_div_iff₀ hπ).mp h_div
    linarith


-- created on 2018-10-31
-- updated on 2026-08-23
