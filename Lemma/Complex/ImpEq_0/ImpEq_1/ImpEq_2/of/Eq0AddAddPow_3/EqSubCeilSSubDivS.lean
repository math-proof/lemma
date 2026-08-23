import sympy.core.power
import sympy.core.numbers
import sympy.functions.elementary.complexes
import sympy.polys.polyroots
import Lemma.Complex.ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3
import Lemma.Complex.CeilSubDivMul3Arg.eq.Ite_0Ite_1Neg1
import Lemma.Complex.ArgMul.eq.Arg.of.Gt_0
import Lemma.Complex.Arg.in.IocNegPiPi
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
  have hmul_half (z : ℂ) :
      ((2 : ℂ)⁻¹ * z) ^ (3 : ℂ)⁻¹ =
        (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ * z ^ (3 : ℂ)⁻¹ := by
    by_cases hz : z = 0
    ·
      subst hz
      simp [(by norm_num : (3 : ℂ) ≠ 0)]
    ·
      rw [cpow_def_of_ne_zero (mul_ne_zero (by norm_num) hz), cpow_def_of_ne_zero hz,
        cpow_def_of_ne_zero (by norm_num : (2 : ℂ)⁻¹ ≠ 0)]
      have hlog : log ((2 : ℂ)⁻¹ * z) = ↑(Real.log (2 : ℝ)⁻¹) + log z := by
        rw [(by norm_num : (2 : ℂ)⁻¹ = (2 : ℝ)⁻¹),
          log_ofReal_mul (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) hz]
      rw [hlog, add_mul, exp_add]
      have hlog2 : log (2 : ℂ)⁻¹ = ↑(Real.log (2 : ℝ)⁻¹) := by
        rw [(by norm_num : (2 : ℂ)⁻¹ = (2 : ℝ)⁻¹),
          ofReal_log (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
      rw [hlog2]
  have hUA : √δ / 2 - q / 2 = (2 : ℂ)⁻¹ * U := by
    simp [U]
    ring
  have hVB : -√δ / 2 - q / 2 = (2 : ℂ)⁻¹ * V := by
    simp [V]
    ring
  have hA : A = (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ * U ^ (3 : ℂ)⁻¹ := by
    simp only [A]
    rw [hUA, hmul_half]
  have hB : B = (2 : ℂ)⁻¹ ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹ := by
    simp only [B]
    rw [hVB, hmul_half]
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
  have hite := CeilSubDivMul3Arg.eq.Ite_0Ite_1Neg1 (p := p) (q := q)
  have hd :
      d =
        ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
          if p * (⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then
            (0 : ℤ)
          else if arg U + arg V > π then
            1
          else
            -1 := by
    simp only [d]
    rw [harg, hite]
  have hceil_bound (z : ℂ) :
      -1 ≤ ⌈3 * arg z / (2 * π) - (1 / 2 : ℝ)⌉ ∧
        ⌈3 * arg z / (2 * π) - (1 / 2 : ℝ)⌉ ≤ 1 := by
    have hmem := Arg.in.IocNegPiPi z
    have hπ : (0 : ℝ) < π := Real.pi_pos
    have h2π : (0 : ℝ) < 2 * π := by linarith
    have hdiv : 3 * arg z / (2 * π) = 3 * (arg z / (2 * π)) := by ring
    have hx_le : 3 * arg z / (2 * π) - 1 / 2 ≤ (↑(1 : ℤ) : ℝ) := by
      have hle : arg z / (2 * π) ≤ π / (2 * π) :=
        div_le_div_of_nonneg_right hmem.2 (le_of_lt h2π)
      have hhalf : π / (2 * π) = (1 / 2 : ℝ) := by field_simp
      have : arg z / (2 * π) ≤ 1 / 2 := by
        rwa [hhalf] at hle
      have : 3 * (arg z / (2 * π)) ≤ 3 / 2 := by
        nlinarith
      rw [hdiv]
      linarith
    have hx_gt : (↑(-2 : ℤ) : ℝ) < 3 * arg z / (2 * π) - 1 / 2 := by
      have hlt : (-π) / (2 * π) < arg z / (2 * π) :=
        div_lt_div_of_pos_right hmem.1 h2π
      have hhalf : (-π) / (2 * π) = (-1 / 2 : ℝ) := by field_simp
      have : -1 / 2 < arg z / (2 * π) := by
        rwa [hhalf] at hlt
      rw [hdiv]
      linarith
    refine ⟨?_, ?_⟩
    ·
      have : (-2 : ℤ) < ⌈3 * arg z / (2 * π) - (1 / 2 : ℝ)⌉ :=
        (Int.lt_ceil (z := -2)).mpr hx_gt
      omega
    ·
      exact (Int.ceil_le (z := 1)).mpr hx_le
  have hmod0 : d % 3 = 0 → d = 0 := by
    intro hmod
    have hp := hceil_bound (-p / 3)
    have hAB' := hceil_bound (A * B)
    have hlo : -2 ≤ d := by
      simp only [d]
      omega
    have hhi : d ≤ 2 := by
      simp only [d]
      omega
    omega
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
-- updated on 2026-08-22
