import sympy.core.numbers
import sympy.core.power
import sympy.polys.polyroots
import Lemma.Algebra.Ceil_Arg.eq.Ite.of.Ne_0
import Lemma.Nat.Eq_0.is.EqMul.of.Ne_0
import Lemma.Complex.EqSquareSqrt
open Algebra Complex Nat


@[main]
private lemma main
  {p q : ℂ} :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let U : ℂ := √δ - q
  let V : ℂ := -√δ - q
  ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉ =
    if p * (⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then
      (0 : ℤ)
    else if arg U + arg V > π then
      1
    else
      -1 := by
-- proof
  intro δ U V
  classical
  by_cases hp : p = 0
  ·
    have hexp : (3 : ℂ)⁻¹ ≠ 0 := by norm_num
    have hz : (0 : ℂ) ^ (3 : ℂ)⁻¹ = 0 := zero_cpow hexp
    have hsq : √δ * √δ = δ := by
      simpa [pow_two] using (EqSquareSqrt : (√δ)² = δ)
    have hUV : U * V = -(4 * p ^ 3 / 27) := by
      simp only [U, V]
      rw [show (√δ - q) * (-√δ - q) = q ^ 2 - √δ * √δ by ring, hsq]
      simp only [δ]
      ring
    have hUV0 : U * V = 0 := by
      simp [hUV, hp]
    have hprod : U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹ = 0 := by
      rcases mul_eq_zero.mp hUV0 with hU | hV
      ·
        simp [hU, hz]
      ·
        simp [hV, hz]
    have harg : arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) = 0 := by
      rw [hprod, arg_zero]
    have hceil0 : ⌈(-1 / 2 : ℝ)⌉ = 0 := by
      apply Int.ceil_eq_iff.mpr
      constructor <;> norm_num
    have hsimp :
        3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2 = -1 / 2 := by
      rw [harg]
      ring
    rw [hsimp, hceil0]
    have hcond : p * (⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ : ℂ) = 0 := by
      simp [hp]
    rw [if_pos hcond]
  ·
    have h := Ceil_Arg.eq.Ite.of.Ne_0 (p := p) (q := q) hp
    simp only [δ, U, V] at h ⊢
    rw [h]
    refine if_congr ?_ rfl rfl
    rw [← Int.cast_eq_zero (α := ℂ), mul_comm p]
    exact Eq_0.is.EqMul.of.Ne_0 hp


-- created on 2018-11-09
-- updated on 2026-08-21
