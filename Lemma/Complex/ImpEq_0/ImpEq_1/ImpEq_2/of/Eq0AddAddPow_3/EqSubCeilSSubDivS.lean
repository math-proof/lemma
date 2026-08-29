import Lemma.Complex.ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3
import Lemma.Complex.AbsSubCeilSSubDivMul3Arg.le.Two
import Lemma.Int.Eq_0.of.Mod_3.eq.Zero.LeAbs_2
open Complex


/--
Cardano's formula for solving cubic equations
-/
@[main]
private lemma main
  {x p q : ℂ}
-- given
  (h : x ^ 3 + p * x + q = 0) :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let d : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  (d % 3 = 0 →
      x = A + B ∨
        x = A * ω + B * ~ω ∨
        x = A * ~ω + B * ω) ∧
    (d % 3 = 1 →
      x = A * ω + B ∨
        x = A * ~ω + B * ~ω ∨
        x = A + B * ω) ∧
    (d % 3 = 2 →
      x = A * ~ω + B ∨
        x = A + B * ~ω ∨
        x = A * ω + B * ω) := by
-- proof
  intro δ A B d ω
  let U : ℂ := √δ - q
  let V : ℂ := -√δ - q
  have hUA : √δ / 2 - q / 2 = (2 : ℂ)⁻¹ * U := by
    simp [U]
    ring
  have hVB : -√δ / 2 - q / 2 = (2 : ℂ)⁻¹ * V := by
    simp [V]
    ring
  have hA : A = (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ * U ^ (3 : ℂ)⁻¹ := by
    simp only [A]
    rw [hUA, (by norm_num : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hB : B = (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹ := by
    simp only [B]
    rw [hVB, (by norm_num : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hcbrt : (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) := by
    rw [show (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹) from by norm_num,
      show (3 : ℂ)⁻¹ = ↑((3 : ℝ)⁻¹) from by norm_num,
      ofReal_cpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hAB :
      A * B =
        ↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) *
          (↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) * (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹)) := by
    rw [hA, hB, hcbrt]
    ring
  have harg : arg (A * B) = arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) := by
    rw [hAB, ArgMul.eq.Arg.of.Gt_0 hpos, ArgMul.eq.Arg.of.Gt_0 hpos]
  have hd :
      d =
        ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
          ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉ := by
    simp only [d]
    rw [harg]
  have hΔ : |d| ≤ 2 := by
    simp only [d]
    apply AbsSubCeilSSubDivMul3Arg.le.Two
  have hmod0 := Int.Eq_0.of.Mod_3.eq.Zero.LeAbs_2 hΔ
  have hC := ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3 h
  rw [hd]
  simp only [A, B, ω, δ]
  obtain ⟨h0, h1, h2⟩ := hC
  refine ⟨?_, h1, h2⟩
  intro hmod
  apply h0
  have hd0 := hmod0
  simp only [hd] at hd0
  exact hd0 hmod


-- created on 2018-11-15
-- updated on 2026-08-29
