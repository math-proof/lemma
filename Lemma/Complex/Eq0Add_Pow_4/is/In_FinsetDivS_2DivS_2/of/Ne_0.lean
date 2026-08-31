import Lemma.Complex.Eq0Add_Pow_3.is.In_Finset_SubSAddMulS
import Lemma.Complex.Eq_SquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0
import Lemma.Complex.Eq0Add_Mul_Square.is.In_FinsetDivS_Mul2.of.Ne_0
import Lemma.Complex.PowMul.eq.MulPowS.of.Gt_0
import Lemma.Int.SquareNeg.eq.Square
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0
import Lemma.Set.In_Finset.is.Or_OrEqS
open Complex Int Rat Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Pow_4.is.In_FinsetDivS_2DivS_2.of.Ne_0 |
| comm | Complex.In_FinsetDivS_2DivS_2.is.Eq0Add_Pow_4.of.Ne_0 |
| mp | Complex.In_FinsetDivS_2DivS_2.of.Eq0Add_Pow_4.Ne_0 |
| mpr | Complex.Eq0Add_Pow_4.of.In_FinsetDivS_2DivS_2.Ne_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  {x α β γ : ℂ}
-- given
  (hβ : β ≠ 0) :
-- imply
  γ + β * x + α * x ^ 2 + x ^ 4 = 0 ↔
    let p := -4 * γ - α ^ 2 / 3
    let q := -2 * α ^ 3 / 27 + 8 * α * γ / 3 - β ^ 2
    let δ := 4 * p ^ 3 / 27 + q ^ 2
    let A := ∛((-q + √δ) / 2)
    let B := ∛((-q - √δ) / 2)
    let k := ⌈3 * arg (-p) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    let ω := (I * (2 * π / 3)).exp
    let y := A * ω ^ k + B
    let y₀ := -2 * α / 3 + y
    let y₁ := 4 * α / 3 + y
    x ∈ ({(√(2 * β / √y₀ - y₁) - √y₀) / 2, (-√(2 * β / √y₀ - y₁) - √y₀) / 2, (√(-2 * β / √y₀ - y₁) + √y₀) / 2, (-√(-2 * β / √y₀ - y₁) + √y₀) / 2} : Set ℂ) := by
-- proof
  extract_lets p q δ A B k ω y y₀ y₁
  simp only [DivSub.eq.SubDivS, DivAdd.eq.AddDivS]
  let cr := -β ^ 2 / 8 + α * γ / 2
  let ar := -α / 2
  let br := -γ
  let pc := br - ar ^ 2 / 3
  let qc := 2 * ar ^ 3 / 27 - ar * br / 3 + cr
  let δc := 4 * pc ^ 3 / 27 + qc ^ 2
  let Ac := ∛((-qc + √δc) / 2)
  let Bc := ∛((-qc - √δc) / 2)
  have h8 : ∛(8 : ℂ) = 2 := by
    rw [(by norm_num : (8 : ℂ) = (2 : ℂ) ^ 3)]
    apply pow_cpow_nat_inv (by norm_num) <;>
    ·
      simp
      linarith [Real.pi_pos]
  have hsqrt : √δ = 8 * √δc := by
    have h64 : (64 : ℂ) ^ (2 : ℂ)⁻¹ = 8 := by
      rw [(by norm_num : (64 : ℂ) = (8 : ℂ) ^ 2)]
      apply pow_cpow_nat_inv (by norm_num) <;>
      ·
        simp
        linarith [Real.pi_pos]
    have hmul64 (w : ℂ) : ((64 : ℂ) * w) ^ (2 : ℂ)⁻¹ = (64 : ℂ) ^ (2 : ℂ)⁻¹ * w ^ (2 : ℂ)⁻¹ := by apply PowMul.eq.MulPowS.of.Gt_0 (by norm_num)
    simp only [Root.sqrt]
    grind
  have hmul8 (w : ℂ) : ∛((8 : ℂ) * w) = ∛(8 : ℂ) * ∛w := by apply PowMul.eq.MulPowS.of.Gt_0 (by norm_num)
  have hA : A = 2 * Ac := by grind
  have hB : B = 2 * Bc := by grind
  let z := Ac * ω ^ k + Bc - ar / 3
  have hcubic : cr + br * z + ar * z ^ 2 + z ^ 3 = 0 := by
    apply Eq0Add_Pow_3.of.In_Finset_SubSAddMulS
    extract_lets
    apply Set.In_Finset.of.Or_OrEqS
    apply Or.inl
    simp only [z, k]
    conv in arg (A * B) =>
      rw [hA, hB]
      ring_nf
      rw [mul_comm]
      erw [ArgMul.eq.Arg.of.Gt_0 (by norm_num)]
    rw [(by grind : -p = 4 * (-pc))]
    erw [ArgMul.eq.Arg.of.Gt_0 (by norm_num)]
  have hy₀z : y₀ = 2 * z - α := by grind
  have hy₁z : y₁ = 2 * z + α := by grind
  have hs2 : (√y₀) ^ 2 = y₀ := EqSquareSqrt
  have hres : z ^ 3 - α * z ^ 2 / 2 - γ * z + (α * γ / 2 - β ^ 2 / 8) = 0 := by
    rw [← hcubic]
    simp only [cr, br, ar]
    ring
  have hsne : √y₀ ≠ 0 := by
    intro hs
    apply Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0 hβ hres
    have : y₀ = 0 := by
      rw [← EqSquareSqrt (x := y₀), hs]
      ring
    rw [hy₀z, sub_eq_zero] at this
    grind
  have hQ : γ + β * x + α * x ^ 2 + x ^ 4 = (x ^ 2 + √y₀ * x + z - β / (2 * √y₀)) * (x ^ 2 - √y₀ * x + z + β / (2 * √y₀)) := calc
    _ = (x ^ 2 + z) ^ 2 - ((2 * z - α) * x ^ 2 + (-β) * x + (z ^ 2 - γ)) := by
      rw [Nat.SquareAdd.eq.AddAddSquareS_MulMul2]
      ring
    _ = (x ^ 2 + z) ^ 2 - (√(2 * z - α) * x + (-β) / (2 * √(2 * z - α))) ^ 2 := by
      rw [Eq_SquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0 (x := x) (by grind) (by grind)]
    _ = (x ^ 2 + z) ^ 2 - (√y₀ * x - β / (2 * √y₀)) ^ 2 := by
      grind
    _ = (x ^ 2 + √y₀ * x + z - β / (2 * √y₀)) * (x ^ 2 - √y₀ * x + z + β / (2 * √y₀)) := by
      ring
  have hsum : x ^ 2 + √y₀ * x + z - β / (2 * √y₀) = 0 ↔ x ∈ ({(√(2 * β / √y₀ - y₁) - √y₀) / 2, (-√(2 * β / √y₀ - y₁) - √y₀) / 2} : Set ℂ) := by
    have h := Eq0Add_Mul_Square.is.In_FinsetDivS_Mul2.of.Ne_0 (x := x) (a := (1 : ℂ)) (b := √y₀) (c := z - β / (2 * √y₀)) one_ne_zero
    extract_lets Δ at h
    have hDelta : Δ = 2 * β / √y₀ - y₁ := by
      simp only [Δ]
      rw [hs2, hy₀z, hy₁z]
      field_simp [hsne]
      ring
    rw [hDelta] at h
    convert h using 1 <;> grind
  have hdiff : x ^ 2 - √y₀ * x + z + β / (2 * √y₀) = 0 ↔ x ∈ ({(√(-2 * β / √y₀ - y₁) + √y₀) / 2, (-√(-2 * β / √y₀ - y₁) + √y₀) / 2} : Set ℂ) := by
    have h := Eq0Add_Mul_Square.is.In_FinsetDivS_Mul2.of.Ne_0 (x := x) (a := (1 : ℂ)) (b := -√y₀) (c := z + β / (2 * √y₀)) one_ne_zero
    extract_lets Δ at h
    have hDelta : Δ = -2 * β / √y₀ - y₁ := by
      simp only [Δ]
      rw [Int.SquareNeg.eq.Square, hs2, hy₀z, hy₁z]
      field_simp [hsne]
      ring
    rw [hDelta] at h
    convert h using 1 <;> grind
  simp only [DivSub.eq.SubDivS, DivAdd.eq.AddDivS] at hsum hdiff
  rw [hQ, Nat.Mul.eq.Zero.is.OrEqS_0, hsum, hdiff]
  simp
  tauto


-- created on 2018-11-27
-- updated on 2026-08-31
