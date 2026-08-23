import sympy.core.numbers
import Lemma.Complex.MulPowS_Inv3.eq.MulPow_Inv3.of.EqCeilSubDivAddArgS.Ne_0.Ne_0
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
        by_cases hA : A = 0
        ·
          simp [hA, hz]
        ·
          by_cases hB : B = 0
          ·
            simp [hB, hz]
          ·
            simpa using MulPowS_Inv3.eq.MulPow_Inv3.of.EqCeilSubDivAddArgS.Ne_0.Ne_0.zero hA hB hd0
  ·
    have ⟨hA, hrest⟩ := not_or.mp h0
    have ⟨hB, hd0⟩ := not_or.mp hrest
    have hd1 : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 1 :=
      (GtAddArgS.is.EqCeilSubDivS (A := A) (B := B)).mp hgt
    simpa using MulPowS_Inv3.eq.MulPow_Inv3.of.EqCeilSubDivAddArgS.Ne_0.Ne_0 hA hB hd1
  ·
    have ⟨hA, hrest⟩ := not_or.mp h0
    have ⟨hB, hd0⟩ := not_or.mp hrest
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
    simpa using MulPowS_Inv3.eq.MulPow_Inv3.of.EqCeilSubDivAddArgS.Ne_0.Ne_0.neg hA hB hdneg


-- created on 2018-11-01
-- updated on 2026-08-20
