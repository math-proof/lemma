import Lemma.Bool.NotOr.is.AndNotS
import Lemma.Complex.ExpMulIDivMulNeg2Pi3.eq.Sub_MulI
import Lemma.Complex.GtAddArgS.is.EqCeilSubDivS
import Lemma.Complex.MulPowS_Inv3.eq.MulPowS.of.EqCeilSubDivAddArgS
import Lemma.Complex.OrEqSCeil.of.CeilSubDivAddArgS.ne.Zero
open Bool Complex


@[main]
private lemma main
  {A B : ℂ} :
-- imply
  ∛A * ∛B = ∛(A * B) *
      if A = 0 ∨ B = 0 ∨ ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 0 then
        (1 : ℂ)
      else if arg A + arg B > π then
        ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ)
      else
        ↑(-(1 / 2 : ℝ)) - I * ↑(√3 / 2 : ℝ) := by
-- proof
  have hz : ∛(0 : ℂ) = 0 := by
    simp only [Root.cubic]
    apply zero_cpow (by norm_num)
  rw [MulPowS_Inv3.eq.MulPowS.of.EqCeilSubDivAddArgS (d := ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉) rfl]
  split_ifs with h0 hgt
  ·
    obtain hA | h0 := h0
    ·
      grind
    ·
      obtain hB | hd0 := h0
      ·
        grind
      ·
        rw [hd0, zpow_zero]
  ·
    rw [EqCeilSubDivS.of.GtAddArgS (A := A) (B := B) hgt, zpow_one]
  ·
    obtain ⟨_, hrest⟩ := AndNotS.of.NotOr h0
    obtain ⟨_, hdne⟩ := AndNotS.of.NotOr hrest
    have hor := OrEqSCeil.of.CeilSubDivAddArgS.ne.Zero hdne
    have hdneg : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = -1 := by
      obtain h | h := hor
      ·
        apply (hgt (GtAddArgS.of.EqCeilSubDivS (A := A) (B := B) h)).elim
      ·
        apply h
    rw [hdneg, zpow_neg_one]
    simp only [Root.sqrt]
    rw [Add_MulI.eq.ExpMulIDivMul2Pi3, ← exp_neg]
    have : -(I * (2 * π / 3)) = I * (-2 * π / 3) := by
      ring
    rw [this, ExpMulIDivMulNeg2Pi3.eq.Sub_MulI]


-- created on 2018-11-01
-- updated on 2026-08-29
