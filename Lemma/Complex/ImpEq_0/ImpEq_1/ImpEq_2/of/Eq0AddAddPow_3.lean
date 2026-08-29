import Lemma.Complex.ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3.EqSubCeilSSubDivMul3Arg
import Lemma.Complex.PowMul.eq.MulPowS.of.Gt_0
open Complex


@[main]
private lemma main
  {x p q : ℂ}
-- given
  (h : x ^ 3 + p * x + q = 0) :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let U : ℂ := √δ - q
  let V : ℂ := -√δ - q
  let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let ω : ℂ := (I * (2 * π / 3)).exp
  let d : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
  x = A * ω ^ d + B ∨
    x = A * ω ^ (d - 1) + B * ω ∨
    x = A * ω ^ (d + 1) + B * ~ω := by
-- proof
  intro δ U V A B ω d
  have hA : A = (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ * U ^ (3 : ℂ)⁻¹ := by
    simp only [A]
    have : √δ / 2 - q / 2 = (2 : ℂ)⁻¹ * U := by
      simp [U]
      ring
    rw [this, (by norm_num : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hB : B = (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹ := by
    simp only [B]
    have : -√δ / 2 - q / 2 = (2 : ℂ)⁻¹ * V := by
      simp [V]
      ring
    rw [this, (by norm_num : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hcbrt : (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) := by
    rw [(by norm_num : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹)),
      (by norm_num : (3 : ℂ)⁻¹ = ↑((3 : ℝ)⁻¹)),
      ofReal_cpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹) := by
    apply Real.rpow_pos_of_pos
    norm_num
  have harg : arg (A * B) = arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) := by
    have : A * B =
        ↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) *
          (↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) * (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹)) := by
      rw [hA, hB, hcbrt]
      ring
    rw [this, ArgMul.eq.Arg.of.Gt_0 hpos, ArgMul.eq.Arg.of.Gt_0 hpos]
  apply ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3.EqSubCeilSSubDivMul3Arg.cardano (d := d) h
  ·
    simp [d]
    rw [harg]


-- created on 2018-11-24
-- updated on 2026-08-29
