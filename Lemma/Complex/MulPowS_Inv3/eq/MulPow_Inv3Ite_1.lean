import Lemma.Complex.MulPowS_Inv3.eq.MulPowS.of.EqCeilSubDivAddArgS
import Lemma.Complex.OrEqSCeil.of.CeilSubDivAddArgS.ne.Zero
import Lemma.Complex.GtAddArgS.is.EqCeilSubDivS
open Complex


@[main]
private lemma main
  {A B : ℂ} :
-- imply
  A ^ (3 : ℂ)⁻¹ * B ^ (3 : ℂ)⁻¹ =
    (A * B) ^ (3 : ℂ)⁻¹ *
      if A = 0 ∨ B = 0 ∨ ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 0 then
        (1 : ℂ)
      else if arg A + arg B > π then
        -(1 / 2) + I * ↑(√3) / 2
      else
        -(1 / 2) - I * ↑(√3) / 2 := by
-- proof
  have hexp : (3 : ℂ)⁻¹ ≠ 0 := by norm_num
  have hz : (0 : ℂ) ^ (3 : ℂ)⁻¹ = 0 := zero_cpow hexp
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  have h3r : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hre : ω.re = -(1 / 2) := by
    simp only [ω, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hω1 : ω = -(1 / 2) + I * ↑(√3) / 2 := by
    apply Complex.ext <;> simp [hre, him]
  have hωinv : ω⁻¹ = -(1 / 2) - I * ↑(√3) / 2 := by
    have hstar : ~ω = -(1 / 2) - I * ↑(√3) / 2 := by
      apply Complex.ext <;> simp [conj_re, conj_im, hre, him]
    have hmul : ω * ~ω = 1 := by
      rw [mul_conj, ← ofReal_one]
      congr 1
      rw [normSq_apply, hre, him]
      ring_nf
      rw [h3r]
      ring
    exact (inv_eq_of_mul_eq_one_right hmul).trans hstar
  split_ifs with h0 hgt
  ·
    rcases h0 with hA | h0
    ·
      simp [hA, hz]
    ·
      rcases h0 with hB | hd0
      ·
        simp [hB, hz]
      ·
        simpa using MulPowS_Inv3.eq.MulPowS.of.EqCeilSubDivAddArgS hd0
  ·
    have hd1 : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 1 :=
      (GtAddArgS.is.EqCeilSubDivS (A := A) (B := B)).mp hgt
    have h := MulPowS_Inv3.eq.MulPowS.of.EqCeilSubDivAddArgS hd1
    convert h
    rw [zpow_one]
    exact hω1.symm
  ·
    have ⟨_, hrest⟩ := not_or.mp h0
    have ⟨_, hd0⟩ := not_or.mp hrest
    have hor := OrEqSCeil.of.CeilSubDivAddArgS.ne.Zero hd0
    have hdne1 : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ ≠ 1 := by
      intro hd1
      exact hgt ((GtAddArgS.is.EqCeilSubDivS (A := A) (B := B)).mpr hd1)
    have hdneg : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = -1 := by
      rcases hor with h | h
      ·
        contradiction
      ·
        exact h
    have h := MulPowS_Inv3.eq.MulPowS.of.EqCeilSubDivAddArgS hdneg
    convert h
    rw [zpow_neg_one]
    exact hωinv.symm


-- created on 2018-11-01
-- updated on 2026-08-29
