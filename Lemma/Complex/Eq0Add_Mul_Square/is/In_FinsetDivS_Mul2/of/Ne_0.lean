import Lemma.Complex.EqSquare.is.In_FinsetSqrt_NegSqrt
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
import Lemma.Set.In_Finset.is.OrEqS
open Int Nat Rat Complex Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Mul_Square.is.In_FinsetDivS_Mul2.of.Ne_0 |
| comm | Complex.In_FinsetDivS_Mul2.is.Eq0Add_Mul_Square.of.Ne_0 |
| mp | Complex.In_FinsetDivS_Mul2.of.Eq0Add_Mul_Square.Ne_0 |
| mpr | Complex.Eq0Add_Mul_Square.of.In_FinsetDivS_Mul2.Ne_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  {x a b c : ℂ}
-- given
  (h₀ : a ≠ 0) :
-- imply
  c + b * x + a * x² = 0 ↔
    let Δ := b² - 4 * a * c
    x ∈ ({(-b + √Δ) / (2 * a), (-b - √Δ) / (2 * a)} : Set ℂ) := by
-- proof
  extract_lets Δ
  have h₂ : (2 : ℂ) * a ≠ 0 := by simp [h₀]
  have h₄ : (4 : ℂ) * a ≠ 0 := by simp [h₀]
  have hid : (2 * a * x + b)² - Δ = 4 * a * (c + b * x + a * x²) := by
    simp only [Δ]
    ring
  have hlin (z : ℂ) : 2 * a * x + b = z ↔ x = (-b + z) / (2 * a) := by
    constructor
    ·
      intro h
      apply Eq_Div.of.EqMul.Ne_0.left h₂
      rw [← h]
      ring
    ·
      intro h
      rw [h]
      field_simp [h₂]
      ring
  have hsq : c + b * x + a * x² = 0 ↔ (2 * a * x + b)² = Δ := by
    rw [Eq.is.Sub.eq.Zero (a := (2 * a * x + b)²) (b := Δ), hid, Mul.eq.Zero.is.OrEqS_0]
    simp [h₄]
  rw [hsq, EqSquare.is.In_FinsetSqrt_NegSqrt, In_Finset.is.OrEqS, hlin √Δ, hlin (-√Δ)]
  rw [(by ring : -b + -√Δ = -b - √Δ), OrEqS.is.In_Finset]


-- created on 2018-08-15
-- updated on 2026-08-31
