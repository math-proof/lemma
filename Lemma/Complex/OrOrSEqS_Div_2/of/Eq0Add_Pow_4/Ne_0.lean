import Lemma.Complex.Eq0Add_Pow_3.of.Eq_SubAdd_Pow_SubCeilSSubDivMul3Arg
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
  let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
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
  have h' : x ^ 4 + α * x ^ 2 + β * x + γ = 0 := by
    rw [(by ring : x ^ 4 + α * x ^ 2 + β * x + γ = γ + β * x + α * x ^ 2 + x ^ 4)]
    apply h
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
  have h64 : (64 : ℂ) ^ (2 : ℂ)⁻¹ = 8 := by
    have h64' : ((8 : ℂ) ^ 2) ^ (2 : ℂ)⁻¹ = 8 := by
      apply pow_cpow_nat_inv (by norm_num) <;>
      ·
        simp
        linarith [Real.pi_pos]
    convert h64'
    norm_num
  have hmul8 (w : ℂ) : ∛((8 : ℂ) * w) = ∛(8 : ℂ) * ∛w := by
    rw [(by norm_num : (8 : ℂ) = ↑(8 : ℝ))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hmul64 (w : ℂ) : ((64 : ℂ) * w) ^ (2 : ℂ)⁻¹ = (64 : ℂ) ^ (2 : ℂ)⁻¹ * w ^ (2 : ℂ)⁻¹ := by
    rw [(by norm_num : (64 : ℂ) = ↑(64 : ℝ))]
    apply PowMul.eq.MulPowS.of.Gt_0
    norm_num
  have hdelta64 : δ = 64 * δc := by
    grind
  have hmid : q = 8 * qc := by
    grind
  have hsqrt : √δ = 8 * √δc := by
    rw [hdelta64]
    simp only [Root.sqrt]
    rw [hmul64, h64]
  have hU : U = (8 : ℂ) * ((-qc + √δc) / 2) := by
    grind
  have hV : V = (8 : ℂ) * ((-qc - √δc) / 2) := by
    grind
  have hA : A = 2 * Ac := by
    simp only [A, Ac]
    simp_all [Root.cubic]
    grind
  have hB : B = 2 * Bc := by
    simp only [B, Bc]
    simp_all [Root.cubic]
    grind
  have harg : arg (A * B) = arg (Ac * Bc) := by
    have : A * B = ↑(4 : ℝ) * (Ac * Bc) := by
      rw [hA, hB]
      ring_nf
      norm_num
    rw [this]
    apply ArgMul.eq.Arg.of.Gt_0
    norm_num
  have hargp : arg (-p / 3) = arg (-pc / 3) := by
    have : -p / 3 = (4 : ℂ) * (-pc / 3) := by
      simp only [p, pc]
      ring
    have h4 : (4 : ℂ) = ↑(4 : ℝ) := by
      norm_num
    rw [this, h4]
    apply ArgMul.eq.Arg.of.Gt_0
    norm_num
  let z := Ac * ω ^ k + Bc - ar / 3
  have hcubic : cr + br * z + ar * z ^ 2 + z ^ 3 = 0 := by
    apply Eq0Add_Pow_3.of.Eq_SubAdd_Pow_SubCeilSSubDivMul3Arg
    extract_lets
    have hkceil :
        k =
          ⌈3 * arg (-pc / 3) / (2 * π) - 1 / 2⌉ -
            ⌈3 * arg (Ac * Bc) / (2 * π) - 1 / 2⌉ := by
      simp only [k]
      rw [harg, hargp]
    simp only [z]
    rw [hkceil]
  have hres : z ^ 3 - α * z ^ 2 / 2 - γ * z + (α * γ / 2 - β ^ 2 / 8) = 0 := by
    simp only [ar, br, cr] at hcubic
    convert hcubic using 1
    ring
  have hzne : z ≠ α / 2 :=
    Rat.Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0 hβ hres
  have hyz : y = 2 * (z + ar / 3) := by
    simp only [y, z, hA, hB]
    ring
  have hy0z : y0 = 2 * z - α := by
    simp only [y0, hyz, ar]
    ring
  have hy1z : y1 = 2 * z + α := by
    simp only [y1, hyz, ar]
    ring
  have hy0ne : y0 ≠ 0 := by
    convert Nat.Mul.ne.Zero.of.Ne_0.Ne_0 (a := (2 : ℂ)) (b := z - α / 2) (by norm_num) (Int.Sub.ne.Zero.of.Ne hzne)
    rw [hy0z]
    ring
  have hs2 : (√y0) ^ 2 = y0 := EqSquareSqrt
  have hsne : √y0 ≠ 0 := by
    apply Nat.Ne_0.of.NeSquare_0
    rwa [hs2]
  have hx4 : x ^ 4 = -α * x ^ 2 - β * x - γ := by
    apply Int.Eq_Sub.of.EqAdd
    linear_combination h'
  have heq : (x ^ 2 + z) ^ 2 = (2 * z - α) * x ^ 2 + (-β) * x + (z ^ 2 - γ) := by
    rw [Nat.SquareAdd.eq.AddAddSquareS_MulMul2]
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
  obtain hdiff | hsum := Int.OrEqS_0.of.Square hsqeq
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
    obtain hpos | hneg := hroot
    ·
      refine Or.inr (Or.inl ?_)
      convert hpos using 1
      rw [hDelta]
      ring
    ·
      refine Or.inr (Or.inr ?_)
      convert hneg using 1
      rw [hDelta]
      ring
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
    obtain hpos | hneg := hroot
    ·
      refine Or.inl (Or.inl ?_)
      convert hpos using 1
      rw [hDelta]
      ring
    ·
      refine Or.inl (Or.inr ?_)
      convert hneg using 1
      rw [hDelta]
      ring


-- created on 2018-11-27
-- updated on 2026-08-29
