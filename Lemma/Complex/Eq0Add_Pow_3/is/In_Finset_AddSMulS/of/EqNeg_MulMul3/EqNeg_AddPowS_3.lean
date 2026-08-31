import Lemma.Complex.Add_Conj.eq.Neg1
import Lemma.Complex.Conj.eq.Square
import Lemma.Complex.Mul_Conj.eq.One
import Lemma.Complex.Pow_3.eq.One
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
import Lemma.Set.In_Finset.is.Or_OrEqS
open Complex Int Nat Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Pow_3.is.In_Finset_AddSMulS.of.EqNeg_MulMul3.EqNeg_AddPowS_3 |
| comm | Complex.In_Finset_AddSMulS.is.Eq0Add_Pow_3.of.EqNeg_MulMul3.EqNeg_AddPowS_3 |
| mp | Complex.In_Finset_AddSMulS.of.Eq0Add_Pow_3.EqNeg_MulMul3.EqNeg_AddPowS_3 |
| mpr | Complex.Eq0Add_Pow_3.of.In_Finset_AddSMulS.EqNeg_MulMul3.EqNeg_AddPowS_3 |
-/
@[main, comm, mp, mpr]
private lemma main
  {x p q A B : ℂ}
-- given
  (h₀ : A ^ 3 + B ^ 3 = -q)
  (h₁ : 3 * A * B = -p) :
-- imply
  q + p * x + x ^ 3 = 0 ↔
    let ω := (I * (2 * π / 3)).exp
    x ∈ ({A + B, A * ω + B * ~ω, A * ~ω + B * ω} : Set ℂ) := by
-- proof
  extract_lets ω
  rw [In_Finset.is.Or_OrEqS]
  have hstar : ~ω = ω ^ 2 := Conj.eq.Square
  have hsq' : (~ω) ^ 2 = ω := by
    rw [hstar, ← pow_mul, (by rfl : (2 * 2 : ℕ) = 4)]
    rw [(by rw [(by rfl : (4 : ℕ) = 3 + 1), pow_add, pow_one] : ω ^ 4 = ω ^ 3 * ω), Pow_3.eq.One, one_mul]
  have hc3 : (~ω) ^ 3 = 1 := by
    rw [pow_succ, hsq', Mul_Conj.eq.One]
  have hc4 : (~ω) ^ 4 = ~ω := by
    rw [pow_succ, hc3, one_mul]
  have hc6 : (~ω) ^ 6 = 1 := by
    rw [(by rfl : (6 : ℕ) = 3 + 3), pow_add, hc3, mul_one]
  have hc8 : (~ω) ^ 8 = (~ω) ^ 2 := by
    rw [(by rfl : (8 : ℕ) = 6 + 2), pow_add, hc6, one_mul]
  have cubic_of_sum {A B : ℂ} (hAB : A ^ 3 + B ^ 3 = -q) (hp : 3 * A * B = -p) (hx : x = A + B) :
      q + p * x + x ^ 3 = 0 := by
    subst hx
    calc
      _ = A ^ 3 + B ^ 3 + 3 * A * B * (A + B) + p * (A + B) + q := by
        ring
      _ = (A ^ 3 + B ^ 3 + q) + (3 * A * B + p) * (A + B) := by
        ring
      _ = (-q + q) + (-p + p) * (A + B) := by
        rw [hp, hAB]
      _ = 0 := by
        ring
  constructor
  ·
    intro h
    have hprod : (x - (A + B)) * (x - (A * ω + B * ~ω)) * (x - (A * ~ω + B * ω)) = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
      rw [← hstar.symm, ← hsq']
      ring_nf
      rw [hc8, hc6, hc4, hsq']
      simp only [mul_one]
      rw [← EqSub.of.Eq_Add (y := (-1 : ℂ)) (d := ~ω) (x := ω) (by rw [add_comm, Neg1.eq.Add_Conj])]
      ring
    obtain h0 | h0 := OrEqS_0.of.Mul.eq.Zero (by
      have : q + p * x + x ^ 3 = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
        rw [h₁, h₀]
        ring
      rw [hprod, ← this, h])
    ·
      obtain h0 | h0 := OrEqS_0.of.Mul.eq.Zero h0
      ·
        apply Or.inl
        apply Eq.of.Sub.eq.Zero h0
      ·
        apply Or.inr
        apply Or.inl
        apply Eq.of.Sub.eq.Zero h0
    ·
      apply Or.inr
      apply Or.inr
      apply Eq.of.Sub.eq.Zero h0
  ·
    intro h
    obtain hx | hx | hx := h
    ·
      apply cubic_of_sum h₀ h₁ hx
    ·
      apply cubic_of_sum (A := A * ω) (B := B * ~ω)
      ·
        rw [mul_pow, mul_pow, Pow_3.eq.One, hc3, mul_one, mul_one, h₀]
      ·
        calc
          _ = 3 * A * B * (ω * ~ω) := by
            ring
          _ = 3 * A * B := by
            rw [Mul_Conj.eq.One, mul_one]
          _ = -p := by
            rw [h₁]
      ·
        apply hx
    ·
      apply cubic_of_sum (A := A * ~ω) (B := B * ω)
      ·
        rw [mul_pow, mul_pow, hc3, Pow_3.eq.One, mul_one, mul_one, h₀]
      ·
        calc
          _ = 3 * A * B * (~ω * ω) := by
            ring
          _ = 3 * A * B := by
            rw [mul_comm (~ω), Mul_Conj.eq.One, mul_one]
          _ = -p := by
            rw [h₁]
      ·
        apply hx


-- created on 2026-08-28
-- updated on 2026-08-31
