import sympy.core.power
import sympy.core.numbers
import sympy.polys.polyroots
import Lemma.Complex.EqSquareSqrt
import Lemma.Complex.Or_Eq_NegSqrt.of.EqSquare
import Lemma.Algebra.Eq.of.Eq_Pow.cubic_root.omega
open Complex Algebra


private lemma ferrari_roots
  {x α β γ y0 y1 : ℂ}
  (h : x ^ 4 + α * x ^ 2 + β * x + γ = 0)
  (hβ : β ≠ 0)
  (hres : y0 ^ 3 + 2 * α * y0 ^ 2 + (α ^ 2 - 4 * γ) * y0 - β ^ 2 = 0)
  (hy1 : y1 = y0 + 2 * α) :
    x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
      x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
      x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
      x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 := by
  have hy0 : y0 ≠ 0 := by
    intro hy0
    have : β ^ 2 = 0 := by
      simpa [hy0] using hres
    exact hβ (sq_eq_zero_iff.mp this)
  have hs2 : (√y0) ^ 2 = y0 := EqSquareSqrt
  have hs : √y0 ≠ 0 := by
    intro hs
    have : y0 = 0 := by
      rw [← hs2, hs, sq_eq_zero_iff]
    contradiction
  let Y : ℂ := (y0 + α) / 2
  have hY4 : 4 * y0 * (Y ^ 2 - γ) = β ^ 2 := by
    have hcalc : 4 * y0 * (Y ^ 2 - γ) = y0 * ((y0 + α) ^ 2 - 4 * γ) := by
      simp only [Y]
      field_simp
      ring
    rw [hcalc]
    have hres' : y0 ^ 3 + 2 * α * y0 ^ 2 + (α ^ 2 - 4 * γ) * y0 = β ^ 2 := by
      linear_combination hres
    convert hres' using 1
    ring
  have hγ : Y ^ 2 - β ^ 2 / (4 * y0) = γ := by
    have h4 : (4 : ℂ) * y0 ≠ 0 := mul_ne_zero (by norm_num) hy0
    field_simp [h4]
    linear_combination hY4
  have hexp : (√y0 * x - β / (2 * √y0)) ^ 2 = y0 * x ^ 2 - β * x + β ^ 2 / (4 * y0) := by
    have hcross : 2 * √y0 * x * (β / (2 * √y0)) = β * x := calc
      2 * √y0 * x * (β / (2 * √y0)) = (2 * √y0) / (2 * √y0) * (β * x) := by
        ring
      _ = β * x := by
        field_simp [hs]
    have hsqβ : (β / (2 * √y0)) ^ 2 = β ^ 2 / (4 * y0) := calc
      (β / (2 * √y0)) ^ 2 = β ^ 2 / (2 * √y0) ^ 2 := div_pow _ _ _
      _ = β ^ 2 / (4 * (√y0) ^ 2) := by
        congr 1
        ring
      _ = β ^ 2 / (4 * y0) := by
        rw [hs2]
    calc
      _ = (√y0) ^ 2 * x ^ 2 - 2 * √y0 * x * (β / (2 * √y0)) + (β / (2 * √y0)) ^ 2 := by
        ring
      _ = y0 * x ^ 2 - β * x + β ^ 2 / (4 * y0) := by
        rw [hs2, hcross, hsqβ]
  have hdiff : (x ^ 2 + Y) ^ 2 - (√y0 * x - β / (2 * √y0)) ^ 2 = x ^ 4 + α * x ^ 2 + β * x + γ := by
    have hYα : 2 * Y - y0 = α := by
      simp only [Y]
      ring
    calc
      _ = x ^ 4 + 2 * Y * x ^ 2 + Y ^ 2 - (y0 * x ^ 2 - β * x + β ^ 2 / (4 * y0)) := by
        rw [hexp]
        ring
      _ = x ^ 4 + (2 * Y - y0) * x ^ 2 + β * x + (Y ^ 2 - β ^ 2 / (4 * y0)) := by
        ring
      _ = x ^ 4 + α * x ^ 2 + β * x + γ := by
        rw [hYα, hγ]
  have hprod : (x ^ 2 - √y0 * x + Y + β / (2 * √y0)) * (x ^ 2 + √y0 * x + Y - β / (2 * √y0)) = 0 := by
    have hsq : (x ^ 2 + Y) ^ 2 - (√y0 * x - β / (2 * √y0)) ^ 2 = 0 := by
      rw [hdiff, h]
    convert hsq using 1
    ring
  rcases mul_eq_zero.mp hprod with hf | hf
  ·
    have hsq : (2 * x - √y0) ^ 2 = -2 * β / √y0 - y1 := by
      have h4 : (2 * x - √y0) ^ 2 = 4 * (x ^ 2 - √y0 * x) + (√y0) ^ 2 := by
        ring
      rw [h4, hs2]
      have hx2 : x ^ 2 - √y0 * x = -Y - β / (2 * √y0) := by
        linear_combination hf
      rw [hx2]
      simp only [Y, hy1]
      field_simp [hs, hy0]
      ring
    obtain hpos | hneg := Or_Eq_NegSqrt.of.EqSquare hsq
    ·
      refine Or.inr (Or.inr (Or.inl ?_))
      have : 2 * x = √y0 + √(-2 * β / √y0 - y1) := by
        linear_combination hpos
      have hx : x = (√y0 + √(-2 * β / √y0 - y1)) / 2 := by
        apply eq_div_of_mul_eq (by norm_num : (2 : ℂ) ≠ 0)
        linear_combination this
      convert hx using 1
      ring
    ·
      refine Or.inr (Or.inr (Or.inr ?_))
      have : 2 * x = √y0 - √(-2 * β / √y0 - y1) := by
        linear_combination hneg
      have hx : x = (√y0 - √(-2 * β / √y0 - y1)) / 2 := by
        apply eq_div_of_mul_eq (by norm_num : (2 : ℂ) ≠ 0)
        linear_combination this
      convert hx using 1
      ring
  ·
    have hsq : (2 * x + √y0) ^ 2 = 2 * β / √y0 - y1 := by
      have h4 : (2 * x + √y0) ^ 2 = 4 * (x ^ 2 + √y0 * x) + (√y0) ^ 2 := by
        ring
      rw [h4, hs2]
      have hx2 : x ^ 2 + √y0 * x = -Y + β / (2 * √y0) := by
        linear_combination hf
      rw [hx2]
      simp only [Y, hy1]
      field_simp [hs, hy0]
      ring
    obtain hpos | hneg := Or_Eq_NegSqrt.of.EqSquare hsq
    ·
      refine Or.inl ?_
      have : 2 * x = -√y0 + √(2 * β / √y0 - y1) := by
        linear_combination hpos
      have hx : x = (-√y0 + √(2 * β / √y0 - y1)) / 2 := by
        apply eq_div_of_mul_eq (by norm_num : (2 : ℂ) ≠ 0)
        linear_combination this
      convert hx using 1
      ring
    ·
      refine Or.inr (Or.inl ?_)
      have : 2 * x = -√y0 - √(2 * β / √y0 - y1) := by
        linear_combination hneg
      have hx : x = (-√y0 - √(2 * β / √y0 - y1)) / 2 := by
        apply eq_div_of_mul_eq (by norm_num : (2 : ℂ) ≠ 0)
        linear_combination this
      convert hx using 1
      ring


@[main]
private lemma main
  {x α β γ : ℂ}
-- given
  (h : x ^ 4 + α * x ^ 2 + β * x + γ = 0)
  (hβ : β ≠ 0) :
-- imply
  let δ : ℂ := -(α ^ 2 / 3 + 4 * γ) ^ 3 / 27 + (-α ^ 3 / 27 + 4 * α * γ / 3 - β ^ 2 / 2) ^ 2
  let U : ℂ := α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + √δ
  let V : ℂ := α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - √δ
  let A : ℂ := U ^ (3 : ℂ)⁻¹
  let B : ℂ := V ^ (3 : ℂ)⁻¹
  let ar : ℂ := -α / 2
  let br : ℂ := -γ
  let cr : ℂ := -β ^ 2 / 8 + α * γ / 2
  let p : ℂ := br - ar ^ 2 / 3
  let q : ℂ := 2 * ar ^ 3 / 27 - ar * br / 3 + cr
  let δc : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let Ac : ℂ := (√δc / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let Bc : ℂ := (-√δc / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let D : ℤ := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (Ac * Bc) / (2 * π) - 1 / 2⌉
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  (D = 0 →
    let y : ℂ := A + B
    let y0 : ℂ := -2 * α / 3 + y
    let y1 : ℂ := 4 * α / 3 + y
    x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
      x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
      x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
      x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) ∧
    (D % 3 = 1 →
      let y : ℂ := A * ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) ∧
    (D % 3 = 2 →
      let y : ℂ := A * (starRingEnd ℂ) ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) := by
  intro δ U V A B ar br cr p q δc Ac Bc D ω
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
  have hmul8 (z : ℂ) : ((8 : ℂ) * z) ^ (3 : ℂ)⁻¹ = (8 : ℂ) ^ (3 : ℂ)⁻¹ * z ^ (3 : ℂ)⁻¹ := by
    by_cases hz : z = 0
    ·
      subst hz
      have hne : (3 : ℂ) ≠ 0 := by norm_num
      simp [hne]
    ·
      have h8z : (8 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz
      have h8ne : (8 : ℂ) ≠ 0 := by norm_num
      rw [cpow_def_of_ne_zero h8z, cpow_def_of_ne_zero hz, cpow_def_of_ne_zero h8ne]
      have hlog : log ((8 : ℂ) * z) = ↑(Real.log 8) + log z := by
        have h8' : (8 : ℂ) = (8 : ℝ) := by norm_num
        rw [h8', log_ofReal_mul (by norm_num : (0 : ℝ) < 8) hz]
      rw [hlog, add_mul, exp_add]
      have hlog8 : log (8 : ℂ) = ↑(Real.log 8) := by
        have h8' : (8 : ℂ) = (8 : ℝ) := by norm_num
        rw [h8', ofReal_log (by norm_num : (0 : ℝ) ≤ 8)]
      rw [hlog8]
  have hmul16 (z : ℂ) : ((16 : ℂ) * z) ^ (2 : ℂ)⁻¹ = (16 : ℂ) ^ (2 : ℂ)⁻¹ * z ^ (2 : ℂ)⁻¹ := by
    by_cases hz : z = 0
    ·
      subst hz
      have hne : (2 : ℂ) ≠ 0 := by norm_num
      simp [hne]
    ·
      have h16z : (16 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz
      have h16ne : (16 : ℂ) ≠ 0 := by norm_num
      rw [cpow_def_of_ne_zero h16z, cpow_def_of_ne_zero hz, cpow_def_of_ne_zero h16ne]
      have hlog : log ((16 : ℂ) * z) = ↑(Real.log 16) + log z := by
        have h16' : (16 : ℂ) = (16 : ℝ) := by norm_num
        rw [h16', log_ofReal_mul (by norm_num : (0 : ℝ) < 16) hz]
      rw [hlog, add_mul, exp_add]
      have hlog16 : log (16 : ℂ) = ↑(Real.log 16) := by
        have h16' : (16 : ℂ) = (16 : ℝ) := by norm_num
        rw [h16', ofReal_log (by norm_num : (0 : ℝ) ≤ 16)]
      rw [hlog16]
  have hδ : δ = 16 * δc := by
    simp only [δ, δc, p, q, ar, br, cr]
    ring
  have hmid : α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 = -4 * q := by
    simp only [q, ar, br, cr]
    ring
  have hsqrt : √δ = 4 * √δc := by
    have : √δ = √(16 * δc) := by
      rw [hδ]
    rw [this]
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
  have hAc3 : Ac ^ 3 = √δc / 2 - q / 2 := by
    simp [Ac]
  have hBc3 : Bc ^ 3 = -√δc / 2 - q / 2 := by
    simp [Bc]
  have hsqδc : √δc * √δc = δc := by
    simpa [pow_two] using (EqSquareSqrt : (√δc) ^ 2 = δc)
  have hprod3 : (Ac * Bc) ^ 3 = (-p / 3) ^ 3 := by
    rw [mul_pow, hAc3, hBc3]
    have hmul : (√δc / 2 - q / 2) * (-√δc / 2 - q / 2) = -(δc - q ^ 2) / 4 := calc
      _ = -((√δc / 2) * (√δc / 2) - (q / 2) * (q / 2)) := by
        ring
      _ = -(√δc * √δc / 4 - q ^ 2 / 4) := by
        ring
      _ = -(δc / 4 - q ^ 2 / 4) := by
        rw [hsqδc]
      _ = -(δc - q ^ 2) / 4 := by
        ring
    have hδq : δc - q ^ 2 = 4 * p ^ 3 / 27 := by
      simp [δc]
    rw [hmul, hδq]
    ring
  have hrot := Eq.of.Eq_Pow.cubic_root.omega (A := Ac * Bc) (B := -p / 3) hprod3
  have hωexp : (2 * π * I / 3).exp = ω := by
    have hmul : (2 * π * I / 3 : ℂ) = ↑(2 * π / 3 : ℝ) * I := by
      simp [div_eq_mul_inv]
      ring
    rw [hmul, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hθ : (2 * π / 3 : ℝ) = π - π / 3 := by ring
    rw [hθ, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp [ω]
    ring_nf
    rfl
  have hAB0 : Ac * Bc = (-p / 3) * ω ^ (-D) := by
    have h := hrot
    simp [hωexp] at h
    convert h using 1
    simp [D]
  have hω3 : ω ^ 3 = 1 := by
    rw [← hωexp, ← exp_nat_mul]
    convert exp_two_pi_mul_I using 2
    ring
  have hωne : ω ≠ 0 := by
    rw [← hωexp]
    exact exp_ne_zero _
  have h3r : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hre : ω.re = -(1 / 2) := by
    simp only [ω, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hstar : (starRingEnd ℂ) ω = ω ^ 2 := by
    apply Complex.ext
    ·
      simp [pow_two, mul_re, conj_re, hre, him]
      ring_nf
      rw [h3r]
      ring
    ·
      simp [pow_two, mul_im, conj_im, hre, him]
      ring
  have hωdmod (n : ℤ) : ω ^ n = ω ^ (n % 3) := by
    have hsplit : n % 3 + 3 * (n / 3) = n := by omega
    conv_lhs => rw [← hsplit]
    rw [zpow_add₀ hωne]
    have : ω ^ (3 * (n / 3) : ℤ) = 1 := by
      rw [zpow_mul]
      have h3z : ω ^ (3 : ℤ) = 1 := by
        rw [zpow_ofNat]
        exact hω3
      rw [h3z, one_zpow]
    rw [this, mul_one]
  have hB3 : B ^ 3 = V := by
    simp [B]
  have hUV : U + V = -8 * q := by
    have : U + V = 2 * (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2) := by
      simp only [U, V]
      ring
    rw [this, hmid]
    ring
  have hbranch (A' : ℂ) (hA'3 : A' ^ 3 = U) (hprodAB : 3 * A' * B = -4 * p) (y y0 y1 : ℂ) (hy : y = A' + B) (hy0 : y0 = -2 * α / 3 + y) (hy1 : y1 = 4 * α / 3 + y) : x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
    x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
    x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
    x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 := by
    have hy1' : y1 = y0 + 2 * α := by
      rw [hy0, hy1]
      ring
    have hs : A' + B = y0 + 2 * α / 3 := by
      rw [hy0, hy]
      ring
    have hcube : (A' + B) ^ 3 + 4 * p * (A' + B) + 8 * q = 0 := by
      have hs3 : (A' + B) ^ 3 = A' ^ 3 + B ^ 3 + 3 * A' * B * (A' + B) := by
        ring
      rw [hs3, hA'3, hB3, hUV, hprodAB]
      ring
    have hres : y0 ^ 3 + 2 * α * y0 ^ 2 + (α ^ 2 - 4 * γ) * y0 - β ^ 2 = 0 := by
      have hid : (y0 + 2 * α / 3) ^ 3 + 4 * p * (y0 + 2 * α / 3) + 8 * q = y0 ^ 3 + 2 * α * y0 ^ 2 + (α ^ 2 - 4 * γ) * y0 - β ^ 2 := by
        simp only [p, q, ar, br, cr]
        ring
      rw [← hid, ← hs]
      exact hcube
    exact ferrari_roots h hβ hres hy1'
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hD y y0 y1
    have hA3 : A ^ 3 = U := by
      simp [A]
    have hprodAB : 3 * A * B = -4 * p := by
      have hAB : A * B = 4 * (Ac * Bc) := by
        rw [hA, hB]
        ring
      have h3 : 3 * A * B = 3 * (A * B) := by ring
      rw [h3, hAB, hAB0, hD]
      have : ω ^ (-(0 : ℤ)) = 1 := by
        rw [neg_zero, zpow_zero]
      rw [this]
      ring
    exact hbranch A hA3 hprodAB y y0 y1 rfl rfl rfl
  ·
    intro hD y y0 y1
    let A' : ℂ := A * ω
    have hA'3 : A' ^ 3 = U := by
      simp only [A']
      rw [mul_pow, hω3, mul_one]
      simp [A]
    have hprodAB : 3 * A' * B = -4 * p := by
      have hAB : A * B = 4 * (Ac * Bc) := by
        rw [hA, hB]
        ring
      simp only [A']
      have h3 : 3 * (A * ω) * B = 3 * (A * B) * ω := by ring
      rw [h3, hAB, hAB0]
      have hωD : ω ^ (-D) * ω = 1 := calc
        ω ^ (-D) * ω = ω ^ (-D) * ω ^ (1 : ℤ) := by
          rw [zpow_one]
        _ = ω ^ (-D + 1) := (zpow_add₀ hωne _ _).symm
        _ = ω ^ (1 - D) := by
          congr 1
          ring
        _ = ω ^ ((1 - D) % 3) := hωdmod _
        _ = ω ^ (0 : ℤ) := by
          congr 1
          have : (1 - D) % 3 = 0 := by omega
          exact this
        _ = 1 := zpow_zero _
      calc
        _ = -4 * p * (ω ^ (-D) * ω) := by ring
        _ = -4 * p := by
          rw [hωD]
          ring
    exact hbranch A' hA'3 hprodAB y y0 y1 rfl rfl rfl
  ·
    intro hD y y0 y1
    let A' : ℂ := A * (starRingEnd ℂ) ω
    have hA'3 : A' ^ 3 = U := by
      simp only [A', hstar]
      rw [mul_pow]
      have : (ω ^ 2) ^ 3 = 1 := by
        rw [← pow_mul]
        have : ω ^ 6 = (ω ^ 3) ^ 2 := by rw [← pow_mul]
        rw [this, hω3, one_pow]
      rw [this, mul_one]
      simp [A]
    have hprodAB : 3 * A' * B = -4 * p := by
      have hAB : A * B = 4 * (Ac * Bc) := by
        rw [hA, hB]
        ring
      simp only [A', hstar]
      have h3 : 3 * (A * ω ^ 2) * B = 3 * (A * B) * ω ^ 2 := by ring
      rw [h3, hAB, hAB0]
      have hωD : ω ^ (-D) * ω ^ 2 = 1 := calc
        ω ^ (-D) * ω ^ 2 = ω ^ (-D) * ω ^ (2 : ℤ) := by
          rw [zpow_ofNat]
        _ = ω ^ (-D + 2) := (zpow_add₀ hωne _ _).symm
        _ = ω ^ (2 - D) := by
          congr 1
          ring
        _ = ω ^ ((2 - D) % 3) := hωdmod _
        _ = ω ^ (0 : ℤ) := by
          congr 1
          have : (2 - D) % 3 = 0 := by omega
          exact this
        _ = 1 := zpow_zero _
      calc
        _ = -4 * p * (ω ^ (-D) * ω ^ 2) := by ring
        _ = -4 * p := by
          rw [hωD]
          ring
    exact hbranch A' hA'3 hprodAB y y0 y1 rfl rfl rfl


-- created on 2018-11-27
-- updated on 2026-08-21
