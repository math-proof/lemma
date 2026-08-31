import Lemma.Complex.Eq0Add_Pow_3.is.In_Finset_SubSAddMulS
import Lemma.Complex.Eq_SquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0
import Lemma.Complex.OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0
import Lemma.Complex.PowMul.eq.MulPowS.of.Gt_0
import Lemma.Int.OrEqS_0.of.Square
import Lemma.Int.SquareNeg.eq.Square
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Rat.Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0
open Complex Int Nat Rat


@[main]
private lemma Ferrari
  {x α β γ : ℂ}
-- given
  (hβ : β ≠ 0)
  (h : γ + β * x + α * x ^ 2 + x ^ 4 = 0) :
-- imply
  let p := -4 * γ - α ^ 2 / 3
  let q := -2 * α ^ 3 / 27 + 8 * α * γ / 3 - β ^ 2
  let δ := 4 * p ^ 3 / 27 + q ^ 2
  let A := ∛((-q + √δ) / 2)
  let B := ∛((-q - √δ) / 2)
  let k := ⌈3 * arg (-p) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  let ω := (I * (2 * π / 3)).exp
  let y := A * ω ^ k + B
  let y0 := -2 * α / 3 + y
  let y1 := 4 * α / 3 + y
  (x = (√(2 * β / √y0 - y1) - √y0) / 2 ∨
    x = (-√(2 * β / √y0 - y1) - √y0) / 2) ∨
    x = (√(-2 * β / √y0 - y1) + √y0) / 2 ∨
    x = (-√(-2 * β / √y0 - y1) + √y0) / 2 := by
-- proof
  intro p q δ A B k ω y y0 y1
  simp only [Rat.DivSub.eq.SubDivS, Rat.DivAdd.eq.AddDivS]
  let cr := -β ^ 2 / 8 + α * γ / 2
  let ar := -α / 2
  let br := -γ
  let pc := br - ar ^ 2 / 3
  let qc := 2 * ar ^ 3 / 27 - ar * br / 3 + cr
  let δc := 4 * pc ^ 3 / 27 + qc ^ 2
  let U := (-q + √δ) / 2
  let V := (-q - √δ) / 2
  let Ac := ∛((-qc + √δc) / 2)
  let Bc := ∛((-qc - √δc) / 2)
  have h8 : ∛(8 : ℂ) = 2 := by
    have h8' : ∛((2 : ℂ) ^ 3) = 2 := by
      apply pow_cpow_nat_inv (by norm_num) <;>
      ·
        simp
        linarith [Real.pi_pos]
    convert h8'
    norm_num
  have hsqrt : √δ = 8 * √δc := by
    have h64 : (64 : ℂ) ^ (2 : ℂ)⁻¹ = 8 := by
      have h64' : ((8 : ℂ) ^ 2) ^ (2 : ℂ)⁻¹ = 8 := by
        apply pow_cpow_nat_inv (by norm_num) <;>
        ·
          simp
          linarith [Real.pi_pos]
      convert h64'
      norm_num
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
  have hy0z : y0 = 2 * z - α := by grind
  have hy1z : y1 = 2 * z + α := by grind
  have hs2 : (√y0) ^ 2 = y0 := EqSquareSqrt
  have hsne : √y0 ≠ 0 := by grind
  have heq : (x ^ 2 + z) ^ 2 = (2 * z - α) * x ^ 2 + (-β) * x + (z ^ 2 - γ) := by
    rw [Nat.SquareAdd.eq.AddAddSquareS_MulMul2]
    grind
  obtain hdiff | hsum := Int.OrEqS_0.of.Square (calc
    _ = (2 * z - α) * x ^ 2 + (-β) * x + (z ^ 2 - γ) := heq
    _ = (√(2 * z - α) * x + (-β) / (2 * √(2 * z - α))) ^ 2 := Eq_SquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0 (x := x) (by grind) (by grind)
    _ = (√y0 * x - β / (2 * √y0)) ^ 2 := by
      rw [hy0z]
      ring)
  ·
    have hquad : (z + β / (2 * √y0)) + (-√y0) * x + (1 : ℂ) * x ^ 2 = 0 := by
      convert hdiff using 1
      ring
    have hroot := OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0 (x := x) one_ne_zero hquad
    extract_lets Δ at hroot
    have hDelta : Δ = -2 * β / √y0 - y1 := by
      simp only [Δ]
      rw [Int.SquareNeg.eq.Square, hs2, hy0z, hy1z]
      field_simp [hsne]
      ring
    obtain hpos | hneg := hroot <;> grind
  ·
    have hquad : (z - β / (2 * √y0)) + √y0 * x + (1 : ℂ) * x ^ 2 = 0 := by
      convert hsum using 1
      ring
    have hroot := OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0 (x := x) one_ne_zero hquad
    extract_lets Δ at hroot
    have hDelta : Δ = 2 * β / √y0 - y1 := by
      simp only [Δ]
      rw [hs2, hy0z, hy1z]
      field_simp [hsne]
      ring
    obtain hpos | hneg := hroot <;> grind


-- created on 2018-11-27
-- updated on 2026-08-31
