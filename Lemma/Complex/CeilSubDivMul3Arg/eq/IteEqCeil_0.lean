import Lemma.Complex.MulPowS_Inv3.eq.MulPow_Inv3Ite_1
import Lemma.Complex.ArgPow_Inv.eq.DivArg
import Lemma.Complex.EqArgExpMulI.of.In_Ioc
import Lemma.Complex.ExpMulIDivMulNeg2Pi3.eq.Sub_MulI
import Lemma.Complex.EqSquareSqrt
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
import Lemma.Nat.Ne_0.Ne_0.of.Mul.ne.Zero
import Lemma.Bool.NotOr.is.AndNotS
open Bool Complex Nat


@[main]
private lemma main
  {p q : ℂ} :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let U : ℂ := √δ - q
  let V : ℂ := -√δ - q
  ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉ =
    if ⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ = 0 then
      (0 : ℤ)
    else if arg U + arg V > π then
      1
    else
      -1 := by
-- proof
  intro δ U V
  have hsq : √δ * √δ = δ := by
    simpa [pow_two] using (EqSquareSqrt : (√δ)² = δ)
  have hUV : U * V = -(4 * p ^ 3 / 27) := by grind
  if hp : p = 0 then
    have hz : (0 : ℂ) ^ (3 : ℂ)⁻¹ = 0 := zero_cpow (by norm_num)
    have hUV0 : U * V = 0 := by grind
    have hprod : U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹ = 0 := by
      obtain hU | hV := OrEqS_0.of.Mul.eq.Zero hUV0 <;> grind
    have harg : arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) = 0 := by
      rw [hprod, arg_zero]
    have hceil0 : ⌈(-1 / 2 : ℝ)⌉ = 0 := by
      apply Int.EqCeil.of.Lt.Le <;> norm_num
    have hsimp :
        3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2 = -1 / 2 := by
      rw [harg]
      ring
    rw [hsimp, hceil0]
    have hθ₁ : -π < arg U + arg V := by
      obtain hU0 | hV0 := OrEqS_0.of.Mul.eq.Zero hUV0
      ·
        simpa [hU0, arg_zero] using (Arg.in.IocNegPiPi V).1
      ·
        simpa [hV0, arg_zero] using (Arg.in.IocNegPiPi U).1
    have hθ₂ : arg U + arg V ≤ π := by
      obtain hU0 | hV0 := OrEqS_0.of.Mul.eq.Zero hUV0
      ·
        simpa [hU0, arg_zero] using (Arg.in.IocNegPiPi V).2
      ·
        simpa [hV0, arg_zero] using (Arg.in.IocNegPiPi U).2
    have hcond : ⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ = 0 := by
      have hπ : (0 : ℝ) < π := Real.pi_pos
      have hden : (0 : ℝ) < 2 * π := mul_pos (by norm_num) hπ
      apply Int.EqCeil.of.Lt.Le
      ·
        have := div_lt_div_of_pos_right hθ₁ hden
        have hsimp' : (-π) / (2 * π) = (-1 / 2 : ℝ) := by field_simp
        rw [hsimp'] at this
        linarith
      ·
        have : (arg U + arg V) / (2 * π) ≤ 1 / 2 := (div_le_iff₀ hden).mpr (by linarith [hθ₂])
        linarith
    rw [if_pos hcond]
  else
    have hUV0 : U * V ≠ 0 := by grind
    obtain ⟨hU, hV⟩ := Ne_0.Ne_0.of.Mul.ne.Zero hUV0
    let d : ℤ := ⌈(arg U + arg V) / (2 * π) - 1 / 2⌉
    have hUV_cbrt : (U * V) ^ (3 : ℂ)⁻¹ ≠ 0 := by
      rw [cpow_def_of_ne_zero hUV0]
      apply exp_ne_zero
    have hfac :
        (if U = 0 ∨ V = 0 ∨ d = 0 then (1 : ℂ)
          else if arg U + arg V > π then
            -(1 / 2) + I * ↑(Real.sqrt 3) / 2
          else
            -(1 / 2) - I * ↑(Real.sqrt 3) / 2) ≠ 0 := by
      split_ifs
      ·
        grind
      ·
        have : -(1 / 2) + I * ↑(Real.sqrt 3) / 2 = (I * (2 * π / 3)).exp := by
          trans ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ)
          ·
            simp [mul_div_assoc]
            rfl
          ·
            apply Add_MulI.eq.ExpMulIDivMul2Pi3
        rw [this]
        apply exp_ne_zero
      ·
        have : -(1 / 2) - I * ↑(Real.sqrt 3) / 2 = (I * (-2 * π / 3)).exp := by
          trans ↑(-(1 / 2 : ℝ)) - I * ↑(√3 / 2 : ℝ)
          ·
            simp [mul_div_assoc]
            rfl
          ·
            apply Sub_MulI.eq.ExpMulIDivMulNeg2Pi3
        rw [this]
        apply exp_ne_zero
    have harg_fac :
        arg
            (if U = 0 ∨ V = 0 ∨ d = 0 then (1 : ℂ)
              else if arg U + arg V > π then
                -(1 / 2) + I * ↑(Real.sqrt 3) / 2
              else
                -(1 / 2) - I * ↑(Real.sqrt 3) / 2) =
          2 * π * d / 3 := by
      split_ifs with h0 hgt
      ·
        have hd0 : d = 0 := by grind
        simp [arg_one, hd0]
      ·
        have hd1 : d = 1 := EqCeilSubDivS.of.GtAddArgS (A := U) (B := V) hgt
        rw [hd1]
        have : arg (-(1 / 2) + I * ↑(Real.sqrt 3) / 2) = 2 * π / 3 := by
          have : -(1 / 2) + I * ↑(Real.sqrt 3) / 2 = (I * (2 * π / 3)).exp := by
            trans ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ)
            ·
              simp [mul_div_assoc]
              rfl
            ·
              apply Add_MulI.eq.ExpMulIDivMul2Pi3
          rw [this]
          have : (I * (2 * π / 3) : ℂ) = I * (2 * π / 3 : ℝ) := by
            simp [div_eq_mul_inv]
          rw [this]
          apply EqArgExpMulI.of.In_Ioc
          apply Set.In_Ioc.of.Lt.Le <;> linarith [Real.pi_pos]
        rw [this]
        ring
      ·
        obtain ⟨_, hrest⟩ := AndNotS.of.NotOr h0
        obtain ⟨_, hdne⟩ := AndNotS.of.NotOr hrest
        have hdneg : d = -1 := by
          obtain h | h := OrEqSCeil.of.CeilSubDivAddArgS.ne.Zero hdne
          ·
            apply (hgt (GtAddArgS.of.EqCeilSubDivS (A := U) (B := V) h)).elim
          ·
            apply h
        rw [hdneg]
        have : arg (-(1 / 2) - I * ↑(Real.sqrt 3) / 2) = -2 * π / 3 := by
          have : -(1 / 2) - I * ↑(Real.sqrt 3) / 2 = (I * (-2 * π / 3)).exp := by
            trans ↑(-(1 / 2 : ℝ)) - I * ↑(√3 / 2 : ℝ)
            ·
              simp [mul_div_assoc]
              rfl
            ·
              apply Sub_MulI.eq.ExpMulIDivMulNeg2Pi3
          rw [this]
          have : (I * (-2 * π / 3) : ℂ) = I * (-2 * π / 3 : ℝ) := by
            simp [div_eq_mul_inv]
          rw [this]
          apply EqArgExpMulI.of.In_Ioc
          apply Set.In_Ioc.of.Lt.Le <;> linarith [Real.pi_pos]
        rw [this]
        ring
    have harg_prod :
        arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) = (arg U + arg V) / 3 := by
      rw [MulPowS_Inv3.eq.MulPow_Inv3Ite_1 (A := U) (B := V)]
      rw [ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hUV_cbrt hfac]
      have : arg ((U * V) ^ (3 : ℂ)⁻¹) = arg (U * V) / 3 := by
        convert ArgPow_Inv.eq.DivArg (U * V) 3 <;> norm_cast
      rw [this, harg_fac]
      have hargUV := ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hU hV
      have hsum : arg (U * V) / 3 + 2 * π * d / 3 = (arg U + arg V) / 3 := by grind
      have hwrap : ⌈((arg U + arg V) / 3) / (2 * π) - 1 / 2⌉ = 0 := by
        have hsumI := Set.Add.in.Ioc.of.In.In (Arg.in.IocNegPiPi U) (Arg.in.IocNegPiPi V)
        have hπ : (0 : ℝ) < π := Real.pi_pos
        have hden : (0 : ℝ) < 6 * π := mul_pos (by norm_num) hπ
        have ha : ((arg U + arg V) / 3) / (2 * π) - 1 / 2 = (arg U + arg V) / (6 * π) - 1 / 2 := by
          grind
        rw [ha]
        apply Int.EqCeil.of.Lt.Le
        ·
          have hlt : -3 * π < arg U + arg V := by linarith [hsumI.1]
          have := div_lt_div_of_pos_right hlt hden
          grind
        ·
          have hle : arg U + arg V ≤ 3 * π := by linarith [hsumI.2]
          have : (arg U + arg V) / (6 * π) ≤ 1 / 2 := (div_le_iff₀ hden).mpr (by linarith)
          linarith
      simp only [hsum, hwrap, mul_zero, sub_zero, Int.cast_zero]
    rw [harg_prod]
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have hsimp :
        3 * ((arg U + arg V) / 3) / (2 * π) - 1 / 2 =
          (arg U + arg V) / (2 * π) - 1 / 2 := by
      field_simp [h3]
    rw [hsimp]
    split_ifs with hd0 hgt
    ·
      grind
    ·
      apply EqCeilSubDivS.of.GtAddArgS (A := U) (B := V) hgt
    ·
      obtain h | h := OrEqSCeil.of.CeilSubDivAddArgS.ne.Zero (by grind : d ≠ 0)
      ·
        apply (hgt (GtAddArgS.of.EqCeilSubDivS (A := U) (B := V) h)).elim
      ·
        apply h


-- created on 2018-11-08
-- updated on 2026-08-29
