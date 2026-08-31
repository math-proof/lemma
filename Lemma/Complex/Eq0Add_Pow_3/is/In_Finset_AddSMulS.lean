import Lemma.Complex.Eq0Add_Pow_3.is.In_Finset_AddSMulS.of.EqNeg_MulMul3.EqNeg_AddPowS_3
import Lemma.Complex.Eq_Mul_Pow_SubCeilS.of.Pow_3
import Lemma.Complex.EqSquareSqrt
import Lemma.Complex.Mul_Conj.eq.One
import Lemma.Complex.Pow_3.eq.One
open Complex


/--
Cardano's formula for solving cubic equations

| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Pow_3.is.In_Finset_AddSMulS |
| comm | Complex.In_Finset_AddSMulS.is.Eq0Add_Pow_3 |
| mp | Complex.In_Finset_AddSMulS.of.Eq0Add_Pow_3 |
| mpr | Complex.Eq0Add_Pow_3.of.In_Finset_AddSMulS |
-/
@[main, comm, mp, mpr]
private lemma main
  {x p q : ℂ} :
-- imply
  q + p * x + x ^ 3 = 0 ↔
    let δ := 4 * p ^ 3 / 27 + q ^ 2
    let A := ∛((-q + √δ) / 2)
    let B := ∛((-q - √δ) / 2)
    let ω := (I * (2 * π / 3)).exp
    let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    x ∈ ({A * ω ^ k + B, A * ω ^ (k - 1) + B * ω, A * ω ^ (k + 1) + B * ~ω} : Set ℂ) := by
-- proof
  extract_lets δ A B ω k
  have hA3 : A ^ 3 = (-q + √δ) / 2 := by
    simp [A, Root.cubic]
  have hB3 : B ^ 3 = (-q - √δ) / 2 := by
    simp [B, Root.cubic]
  have hA3B3 : A ^ 3 + B ^ 3 = -q := by
    rw [hA3, hB3]
    ring
  have hωexp : (I * (2 * π / 3)).exp = ω := rfl
  have hωne : ω ≠ 0 := by
    apply exp_ne_zero
  apply (Eq0Add_Pow_3.is.In_Finset_AddSMulS.of.EqNeg_MulMul3.EqNeg_AddPowS_3 (A := A * ω ^ k) (B := B) ?_ ?_).trans
  .
    simp only [hωexp]
    have : A * ω ^ k * ~ω + B * ω = A * ω ^ (k - 1) + B * ω := by
      rw [mul_assoc, ← inv_eq_of_mul_eq_one_right Mul_Conj.eq.One, ← zpow_neg_one, ← zpow_add₀ hωne, sub_eq_add_neg]
    have : A * ω ^ (k + 1) + B * ~ω = A * ω ^ k * ω + B * ~ω := by
      rw [mul_assoc, ← zpow_add_one₀ hωne]
    aesop
  ·
    have : (ω ^ k) ^ (3 : ℕ) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, Pow_3.eq.One, one_zpow]
    rw [mul_pow, this, mul_one, hA3B3]
  ·
    have hmul : ((-q + √δ) / 2) * ((-q - √δ) / 2) = -(δ - q ^ 2) / 4 := calc
      _ = -((√δ / 2) * (√δ / 2) - (q / 2) * (q / 2)) := by
        ring
      _ = -(√δ * √δ / 4 - q ^ 2 / 4) := by
        ring
      _ = -(δ / 4 - q ^ 2 / 4) := by
        rw [(by simpa [pow_two] using (EqSquareSqrt : (√δ)² = δ) : √δ * √δ = δ)]
      _ = -(δ - q ^ 2) / 4 := by
        ring
    have h := Eq_Mul_Pow_SubCeilS.of.Pow_3 (A := A * B) (B := -p / 3) (by
      rw [mul_pow, hA3, hB3, hmul, (by simp [δ] : δ - q ^ 2 = 4 * p ^ 3 / 27)]
      ring)
    simp only [hωexp] at h
    calc
      _ = 3 * (A * B * ω ^ k) := by
        ring
      _ = 3 * ((-p / 3) * ω ^ (-k) * ω ^ k) := by
        rw [h]
        simp [k]
      _ = 3 * (-p / 3) := by
        rw [mul_assoc, ← zpow_add₀ hωne]
        simp [neg_add_cancel]
      _ = -p := by
        ring


-- created on 2018-11-15
-- updated on 2026-08-31
