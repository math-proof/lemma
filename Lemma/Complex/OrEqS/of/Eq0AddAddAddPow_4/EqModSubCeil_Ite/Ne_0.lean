import Lemma.Complex.Eq0AddAddAddPow_3.of.Eq_Ite_SubAdd_Pow_Inv3.EqModSubCeil_Ite
import Lemma.Complex.Eq_SquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0
import Lemma.Complex.OrEqS_Div.of.Eq0AddAddMul_Square.Ne_0
import Lemma.Int.OrEqS_0.of.Square
import Lemma.Int.SquareNeg.eq.Square
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Rat.Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0
open Complex Int Nat Rat


/--
Ferrari's formula for one Cardano branch of the depressed quartic

[Quartic formula](https://planetmath.org/QuarticFormula)

[Quartic equation](https://en.wikipedia.org/wiki/Quartic_equation)
-/
@[main]
private lemma main
  {x α β γ : ℂ}
  {d : ℤ}
-- given
  (h₀ : β ≠ 0)
  (h₁ : (
    let ar : ℂ := -α / 2
    let br : ℂ := -γ
    let cr : ℂ := -β ^ 2 / 8 + α * γ / 2
    let p : ℂ := br - ar ^ 2 / 3
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      (
        let q : ℂ := 2 * ar ^ 3 / 27 - ar * br / 3 + cr
        let δc : ℂ := 4 * p ^ 3 / 27 + q ^ 2
        let U : ℂ := √δc - q
        let V : ℂ := -√δc - q
        if p * (⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then
          (0 : ℤ)
        else if arg U + arg V > π then
          1
        else
          -1
      )) % 3 = d)
  (h₂ : x ^ 4 + α * x ^ 2 + β * x + γ = 0) :
-- imply
  let δ : ℂ := -(α ^ 2 / 3 + 4 * γ) ^ 3 / 27 + (-α ^ 3 / 27 + 4 * α * γ / 3 - β ^ 2 / 2) ^ 2
  let U : ℂ := α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + √δ
  let V : ℂ := α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - √δ
  let A : ℂ := U ^ (3 : ℂ)⁻¹
  let B : ℂ := V ^ (3 : ℂ)⁻¹
  let ω : ℂ := ↑(- (1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  let y : ℂ := if d = 0 then A + B else if d = 1 then A * ω + B else A * ~ω + B
  let y0 : ℂ := -2 * α / 3 + y
  let y1 : ℂ := 4 * α / 3 + y
  x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
    x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
    x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
    x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 := by
-- proof
  extract_lets ar br cr at h₁
  intro δ U V A B ω y y0 y1
  let p : ℂ := br - ar ^ 2 / 3
  let q : ℂ := 2 * ar ^ 3 / 27 - ar * br / 3 + cr
  let δc : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let Ac : ℂ := (√δc / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let Bc : ℂ := (-√δc / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let z : ℂ :=
    (if d = 0 then Ac + Bc else if d = 1 then Ac * ω + Bc else Ac * ~ω + Bc) - ar / 3
  have hcubic : z ^ 3 + ar * z ^ 2 + br * z + cr = 0 := by
    apply Eq0AddAddAddPow_3.of.Eq_Ite_SubAdd_Pow_Inv3.EqModSubCeil_Ite (x := z) (a := ar) (b := br) (c := cr) (d := d)
    ·
      convert h₁
    ·
      extract_lets
      simp [z, Ac, Bc]
  have hres : z ^ 3 - α * z ^ 2 / 2 - γ * z + (α * γ / 2 - β ^ 2 / 8) = 0 := by
    simp only [ar, br, cr] at hcubic
    convert hcubic using 1
    ring
  have hzne : z ≠ α / 2 :=
    Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0 h₀ hres
  have h8 : (8 : ℂ) ^ (3 : ℂ)⁻¹ = 2 := by
    have h8' : ((2 : ℂ) ^ 3) ^ (3 : ℂ)⁻¹ = 2 := by
      apply pow_cpow_nat_inv (by norm_num)
      ·
        simp
        linarith [Real.pi_pos]
      ·
        simp
        linarith [Real.pi_pos]
    convert h8'
    norm_num
  have h16 : (16 : ℂ) ^ (2 : ℂ)⁻¹ = 4 := by
    have h16' : ((4 : ℂ) ^ 2) ^ (2 : ℂ)⁻¹ = 4 := by
      apply pow_cpow_nat_inv (by norm_num)
      ·
        simp
        linarith [Real.pi_pos]
      ·
        simp
        linarith [Real.pi_pos]
    convert h16'
    norm_num
  have hmul8 (w : ℂ) : ((8 : ℂ) * w) ^ (3 : ℂ)⁻¹ = (8 : ℂ) ^ (3 : ℂ)⁻¹ * w ^ (3 : ℂ)⁻¹ := by
    rw [(by norm_num : (8 : ℂ) = ↑(8 : ℝ))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hmul16 (w : ℂ) : ((16 : ℂ) * w) ^ (2 : ℂ)⁻¹ = (16 : ℂ) ^ (2 : ℂ)⁻¹ * w ^ (2 : ℂ)⁻¹ := by
    rw [(by norm_num : (16 : ℂ) = ↑(16 : ℝ))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hdelta16 : δ = 16 * δc := by
    simp only [δ, δc, p, q, ar, br, cr]
    ring
  have hmid : α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 = -4 * q := by
    simp only [q, ar, br, cr]
    ring
  have hsqrt : √δ = 4 * √δc := by
    rw [hdelta16]
    simp only [Root.sqrt]
    rw [hmul16, h16]
  have hU : U = (8 : ℂ) * (√δc / 2 - q / 2) := by
    simp only [U]
    rw [hsqrt, hmid]
    ring
  have hV : V = (8 : ℂ) * (-√δc / 2 - q / 2) := by
    simp only [V]
    rw [hsqrt, hmid]
    ring
  have hA : A = 2 * Ac := by
    simp only [A, Ac]
    rw [hU, hmul8, h8]
  have hB : B = 2 * Bc := by
    simp only [B, Bc]
    rw [hV, hmul8, h8]
  have hyz : y = 2 * (z + ar / 3) := by
    simp only [y, z, hA, hB]
    if hD0 : d = 0 then
      simp [hD0]
      ring
    else if hD1 : d = 1 then
      simp [hD1]
      ring
    else
      simp [hD0, hD1]
      ring
  have hy0z : y0 = 2 * z - α := by
    simp only [y0, hyz, ar]
    ring
  have hy1z : y1 = 2 * z + α := by
    simp only [y1, hyz, ar]
    ring
  have hy0ne : y0 ≠ 0 := by
    convert Mul.ne.Zero.of.Ne_0.Ne_0 (a := (2 : ℂ)) (b := z - α / 2) (by norm_num) (Sub.ne.Zero.of.Ne hzne)
    rw [hy0z]
    ring
  have hs2 : (√y0) ^ 2 = y0 := EqSquareSqrt
  have hsne : √y0 ≠ 0 := by
    apply Ne_0.of.NeSquare_0
    rwa [hs2]
  have hx4 : x ^ 4 = -α * x ^ 2 - β * x - γ := by
    apply Eq_Sub.of.EqAdd
    linear_combination h₂
  have heq : (x ^ 2 + z) ^ 2 = (2 * z - α) * x ^ 2 + (-β) * x + (z ^ 2 - γ) := by
    rw [SquareAdd.eq.AddAddSquareS_MulMul2]
    rw [show (x ^ 2) ^ 2 = x ^ 4 by ring, hx4]
    ring
  have hdisc : (-β) ^ 2 - 4 * (2 * z - α) * (z ^ 2 - γ) = 0 := by
    linear_combination -8 * hres
  have hsqeq : (x ^ 2 + z) ^ 2 = (√y0 * x - β / (2 * √y0)) ^ 2 := by
    calc
      _ = (2 * z - α) * x ^ 2 + (-β) * x + (z ^ 2 - γ) := heq
      _ = (√(2 * z - α) * x + (-β) / (2 * √(2 * z - α))) ^ 2 :=
        Eq_SquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0 (x := x) (by rwa [hy0z] at hy0ne) hdisc
      _ = (√y0 * x - β / (2 * √y0)) ^ 2 := by
        rw [hy0z]
        ring
  obtain hdiff | hsum := OrEqS_0.of.Square hsqeq
  ·
    have hquad : (1 : ℂ) * x ^ 2 + (-√y0) * x + (z + β / (2 * √y0)) = 0 := by
      convert hdiff using 1
      ring
    have hroot := OrEqS_Div.of.Eq0AddAddMul_Square.Ne_0 (x := x) one_ne_zero hquad
    extract_lets Δ at hroot
    have hDelta : Δ = -2 * β / √y0 - y1 := by
      simp only [Δ]
      rw [SquareNeg.eq.Square, hs2, hy0z, hy1z]
      field_simp [hsne]
      ring
    obtain hpos | hneg := hroot
    ·
      refine Or.inr (Or.inr (Or.inl ?_))
      convert hpos using 1
      rw [hDelta]
      ring
    ·
      refine Or.inr (Or.inr (Or.inr ?_))
      convert hneg using 1
      rw [hDelta]
      ring
  ·
    have hquad : (1 : ℂ) * x ^ 2 + √y0 * x + (z - β / (2 * √y0)) = 0 := by
      convert hsum using 1
      ring
    have hroot := OrEqS_Div.of.Eq0AddAddMul_Square.Ne_0 (x := x) one_ne_zero hquad
    extract_lets Δ at hroot
    have hDelta : Δ = 2 * β / √y0 - y1 := by
      simp only [Δ]
      rw [hs2, hy0z, hy1z]
      field_simp [hsne]
      ring
    obtain hpos | hneg := hroot
    ·
      refine Or.inl ?_
      convert hpos using 1
      rw [hDelta]
      ring
    ·
      refine Or.inr (Or.inl ?_)
      convert hneg using 1
      rw [hDelta]
      ring


-- created on 2018-11-26
-- updated on 2026-08-28
