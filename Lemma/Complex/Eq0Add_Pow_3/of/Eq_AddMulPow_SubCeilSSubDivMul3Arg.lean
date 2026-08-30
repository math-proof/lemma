import Lemma.Complex.Eq0Add_Pow_3.is.Or_OrEqS_AddMulS.of.EqNeg_MulMul3.EqNeg_AddPowS_3
import Lemma.Complex.EqSquareSqrt
import Lemma.Complex.Eq_Mul_Pow_SubCeilS.of.Pow_3
open Complex


@[main]
private lemma main
  {x p q : ℂ}
-- given
  (h : x =
    let ω := (I * (2 * π / 3)).exp
    let δ := 4 * p ^ 3 / 27 + q ^ 2
    let A := ∛((-q + √δ) / 2)
    let B := ∛((-q - √δ) / 2)
    let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    A * ω ^ k + B) :
-- imply
  q + p * x + x ^ 3 = 0 := by
-- proof
  extract_lets ω δ A B k at h
  have hA3 : A ^ 3 = (-q + √δ) / 2 := by
    simp [A, Root.cubic]
  have hB3 : B ^ 3 = (-q - √δ) / 2 := by
    simp [B, Root.cubic]
  have hA3B3 : A ^ 3 + B ^ 3 = -q := by
    rw [hA3, hB3]
    ring
  have hω3 : ω ^ 3 = 1 := by
    rw [← exp_nat_mul]
    convert exp_two_pi_mul_I using 2
    ring
  have hωne : ω ≠ 0 := exp_ne_zero _
  have hωk3 : (ω ^ k) ^ (3 : ℕ) = 1 := by
    rw [← zpow_ofNat, ← zpow_mul]
    rw [(by ring : (k * 3 : ℤ) = 3 * k)]
    rw [zpow_mul, zpow_ofNat, hω3, one_zpow]
  have hAB : A * B = (-p / 3) * ω ^ (-k) := by
    have hmul : ((-q + √δ) / 2) * ((-q - √δ) / 2) = -(δ - q ^ 2) / 4 := calc
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
    simp [ω, k]
  have hABk : A * B * ω ^ k = -p / 3 := by
    rw [hAB, mul_assoc, ← zpow_add₀ hωne]
    simp [neg_add_cancel]
  apply Eq0Add_Pow_3.of.Or_OrEqS_AddMulS.EqNeg_MulMul3.EqNeg_AddPowS_3 (A := A * ω ^ k) (B := B)
  ·
    rw [mul_pow, hωk3, mul_one, hA3B3]
  ·
    have : 3 * (A * ω ^ k) * B = 3 * (A * B * ω ^ k) := by
      ring
    rw [this, hABk]
    ring
  ·
    apply Or.inl
    apply h


-- created on 2018-11-20
-- updated on 2026-08-30
