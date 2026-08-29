import Lemma.Complex.AbsSubCeilSSubDivMul3Arg.le.Two
import Lemma.Complex.Eq0AddAddPow_3.is.OrEqSAdd.of.EqMul3_Neg.EqAddPowS_3_Neg
import Lemma.Complex.EqSquareSqrt
import Lemma.Complex.Eq_Mul_Pow_SubCeilS.of.Pow_3
import Lemma.Complex.ExpMulIDivMul2Pi3.eq.Add_MulI
import Lemma.Complex.PowMul.eq.MulPowS.of.Gt_0
open Complex


@[main]
private lemma Cardano
  {x p q : ℂ}
  {d : ℤ}
-- given
  (h₀ : ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
    (
      let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
      let U : ℂ := √δ - q
      let V : ℂ := -√δ - q
      ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
    ) = d)
  (h₁ : x =
    let ω : ℂ := (I * (2 * π / 3)).exp
    let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
    let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
    let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
    if d = 0 then A + B else if d % 3 = 1 then A * ω + B else A * ~ω + B):
-- imply
  x ^ 3 + p * x + q = 0 := by
-- proof
  extract_lets δ U V at h₀
  extract_lets ω A B at h₁
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by norm_num) _
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
  have harg : arg (A * B) = arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) := by
    have : A * B =
        ↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) *
          (↑((2 : ℝ)⁻¹ ^ ((3 : ℝ)⁻¹)) * (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹)) := by
      rw [hA, hB, hcbrt]
      ring
    rw [this, ArgMul.eq.Arg.of.Gt_0 hpos, ArgMul.eq.Arg.of.Gt_0 hpos]
  have hA3 : A ^ 3 = √δ / 2 - q / 2 := by
    simp [A]
  have hB3 : B ^ 3 = -√δ / 2 - q / 2 := by
    simp [B]
  have hA3B3 : A ^ 3 + B ^ 3 = -q := by
    rw [hA3, hB3]
    ring
  have hω : ω = ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ) := by
    apply ExpMulIDivMul2Pi3.eq.Add_MulI
  have hω3 : ω ^ 3 = 1 := by
    rw [← exp_nat_mul]
    convert exp_two_pi_mul_I using 2
    ring
  have h3r : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hre : ω.re = -(1 / 2) := by
    simp only [hω, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [hω, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hstar : ~ω = ω ^ 2 := by
    apply ext
    ·
      simp [pow_two, mul_re, conj_re, hre, him]
      ring_nf
      rw [h3r]
      ring
    ·
      simp [pow_two, mul_im, conj_im, hre, him]
      ring
  have hωne : ω ≠ 0 := by
    apply exp_ne_zero
  let d_alg : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  have hd_alg : d_alg = d := by
    simp only [d_alg]
    rw [harg]
    apply h₀
  have hAB : A * B = (-p / 3) * ω ^ (-d_alg) := by
    have hmul : (√δ / 2 - q / 2) * (-√δ / 2 - q / 2) = -(δ - q ^ 2) / 4 := calc
      _ = -((√δ / 2) * (√δ / 2) - (q / 2) * (q / 2)) := by
        ring
      _ = -(√δ * √δ / 4 - q ^ 2 / 4) := by
        ring
      _ = -(δ / 4 - q ^ 2 / 4) := by
        rw [(by simpa [pow_two] using (EqSquareSqrt : (√δ)² = δ) : √δ * √δ = δ)]
      _ = -(δ - q ^ 2) / 4 := by
        ring
    have h :=
      Eq_Mul_Pow_SubCeilS.of.Pow_3 (A := A * B) (B := -p / 3) (by
        rw [mul_pow, hA3, hB3, hmul, (by simp [δ] : δ - q ^ 2 = 4 * p ^ 3 / 27)]
        ring)
    convert h using 1
    simp [ω, d_alg]
  have hABd : A * B * ω ^ d_alg = -p / 3 := by
    rw [hAB, mul_assoc, ← zpow_add₀ hωne]
    simp [neg_add_cancel]
  have hωdmod (n : ℤ) : ω ^ n = ω ^ (n % 3) := by
    conv_lhs => rw [(by omega : n = n % 3 + 3 * (n / 3))]
    rw [zpow_add₀ hωne, (by rw [zpow_mul, zpow_ofNat, hω3, one_zpow] : ω ^ (3 * (n / 3) : ℤ) = 1), mul_one]
  rw [hd_alg] at hABd
  obtain hd0 | hmod | hmod :=
    (by
      have hΔ : |d| ≤ 2 := by
        rw [← hd_alg]
        simp only [d_alg]
        apply AbsSubCeilSSubDivMul3Arg.le.Two
      obtain ⟨hlo, hhi⟩ := Int.LeNeg.Le.of.LeAbs hΔ
      omega :
      d = 0 ∨ d % 3 = 1 ∨ d % 3 = 2)
  ·
    apply Eq0AddAddPow_3.of.OrEqSAdd.EqMul3_Neg.EqAddPowS_3_Neg (A := A) (B := B)
    ·
      apply hA3B3
    ·
      have : A * B = -p / 3 := by
        simpa [(by rw [hd0, zpow_zero] : ω ^ d = 1), mul_one] using hABd
      have : 3 * (A * B) = -p := by
        rw [this]
        ring
      convert this using 1
      ring
    ·
      apply Or.inl
      simpa [hd0] using h₁
  ·
    let A' : ℂ := A * ω
    apply Eq0AddAddPow_3.of.OrEqSAdd.EqMul3_Neg.EqAddPowS_3_Neg (A := A') (B := B)
    ·
      simp only [A']
      rw [mul_pow, hω3, mul_one, hA3B3]
    ·
      simp only [A']
      calc
        _ = 3 * (A * B * ω) := by
          ring
        _ = 3 * (-p / 3) := by
          have : A * B * ω = -p / 3 := by
            simpa [(by rw [hωdmod, hmod, zpow_one] : ω ^ d = ω)] using hABd
          rw [this]
        _ = -p := by
          ring
    ·
      apply Or.inl
      have : d ≠ 0 := by
        intro h
        subst h
        simp at hmod
      simpa [A', hmod, this] using h₁
  ·
    let A' : ℂ := A * ~ω
    apply Eq0AddAddPow_3.of.OrEqSAdd.EqMul3_Neg.EqAddPowS_3_Neg (A := A') (B := B)
    ·
      simp only [A', hstar]
      have : (ω ^ 2) ^ 3 = 1 := by
        rw [← pow_mul, (by rfl : (2 * 3 : ℕ) = 6)]
        rw [(by rw [← pow_mul] : ω ^ 6 = (ω ^ 3) ^ 2), hω3, one_pow]
      rw [mul_pow, this, mul_one, hA3B3]
    ·
      simp only [A', hstar]
      calc
        _ = 3 * (A * B * ω ^ 2) := by
          ring
        _ = 3 * (-p / 3) := by
          have : A * B * ω ^ 2 = -p / 3 := by
            simpa [(by rw [hωdmod d, hmod, zpow_ofNat] : ω ^ d = ω ^ 2)] using hABd
          rw [this]
        _ = -p := by
          ring
    ·
      apply Or.inl
      have : d ≠ 0 := by
        intro h
        subst h
        simp at hmod
      have : d % 3 ≠ 1 := by
        omega
      simpa [A', this, ‹d ≠ 0›] using h₁


-- created on 2018-11-10
-- updated on 2026-08-29
