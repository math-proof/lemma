import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.PowAddDivNeg1'2DivMulISqrt3'2'3.eq.One
import Lemma.Complex.AddAddSquareAddDivNeg1'2DivMulISqrt3'2AddDivNeg1'2DivMulISqrt3'2'1.eq.Zero
import Lemma.Complex.ConjAddDivNeg1'2DivMulISqrt3'2.eq.SquareAddDivNeg1'2DivMulISqrt3'2
import Lemma.Complex.PowPowAddDivNeg1'2DivMulISqrt3'2'3.eq.One
import Lemma.Complex.PowAddDivNeg1'2DivMulISqrt3'2.eq.PowAddDivNeg1'2DivMulISqrt3'2EMod3
import Lemma.Complex.AddPowPowPowPow.eq.Neg
import Lemma.Complex.MulMulPowPowPow.eq.DivNeg3.of.EqSubCeil.Eq_AddDivMul4Pow3'27Square


@[main]
private lemma mod
  {x p q δ A B ω : ℂ}
  {D : ℤ}
-- given
  (hδ : δ = 4 * p ^ 3 / 27 + q ^ 2)
  (hA : A = (δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ))
  (hB : B = (-δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ))
  (hω : ω = -1 / 2 + Complex.I * √3 / 2)
  (hD : D = ⌈3 * arg (-p / 3) / (π * 2) - 1 / 2⌉ - (if p * (⌈(arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q)) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then 0 else if arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q) > π then 1 else -1))
  (h : x ^ 3 + p * x + q = 0) :
-- imply
  (D = 0 → x = A + B ∨ x = A * ω + B * ~ω ∨ x = A * ~ω + B * ω) ∧
  (D % 3 = 1 → x = A * ω + B ∨ x = A * ~ω + B * ~ω ∨ x = A + B * ω) ∧
  (D % 3 = 2 → x = A * ~ω + B ∨ x = A + B * ~ω ∨ x = A * ω + B * ω) := by
-- proof
  have hK := Complex.MulMulPowPowPow.eq.DivNeg3.of.EqSubCeil.Eq_AddDivMul4Pow3'27Square hδ hD.symm
  have hsum := Complex.AddPowPowPowPow.eq.Neg (q := q) (δ := δ)
  rw [← hA, ← hB, ← hω] at hK
  rw [← hA, ← hB] at hsum
  have hω2 : ω ^ 2 + ω + 1 = 0 := hω ▸ Complex.AddAddSquareAddDivNeg1'2DivMulISqrt3'2AddDivNeg1'2DivMulISqrt3'2'1.eq.Zero
  have hω3 : ω ^ 3 = 1 := hω ▸ Complex.PowAddDivNeg1'2DivMulISqrt3'2'3.eq.One
  have hc : ~ω = ω ^ 2 := hω ▸ Complex.ConjAddDivNeg1'2DivMulISqrt3'2.eq.SquareAddDivNeg1'2DivMulISqrt3'2
  have hWm : ω ^ D = ω ^ (D % 3) := hω ▸ Complex.PowAddDivNeg1'2DivMulISqrt3'2.eq.PowAddDivNeg1'2DivMulISqrt3'2EMod3
  have hW3 : (ω ^ D) ^ 3 = 1 := hω ▸ Complex.PowPowAddDivNeg1'2DivMulISqrt3'2'3.eq.One
  set W := ω ^ D with hW_def
  have fac : (x - (A * W + B)) * (x - (A * W * ω + B * ω ^ 2)) * (x - (A * W * ω ^ 2 + B * ω)) = 0 := by
    linear_combination (-(-A * W - B + x) * (-A ^ 2 * W ^ 2 * ω + A ^ 2 * W ^ 2 - A * B * W * ω ^ 2 + A * B * W * ω - A * B * W + A * W * x - B ^ 2 * ω + B ^ 2 + B * x)) * hω2 + h - 3 * x * hK - A ^ 3 * hW3 - hsum
  rw [hc]
  rcases mul_eq_zero.mp fac with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · have e1 : x = A * W + B := by linear_combination h1
      refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
      · rw [hW_def, hd, zpow_zero] at e1
        left; linear_combination e1
      · rw [hWm, hd, zpow_one] at e1
        left; linear_combination e1
      · rw [hWm, hd, zpow_ofNat] at e1
        left; linear_combination e1
    · have e2 : x = A * W * ω + B * ω ^ 2 := by linear_combination h2
      refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
      · rw [hW_def, hd, zpow_zero] at e2
        right; left; linear_combination e2
      · rw [hWm, hd, zpow_one] at e2
        right; left; linear_combination e2
      · rw [hWm, hd, zpow_ofNat] at e2
        right; left; linear_combination e2 + A * hω3
  · have e3 : x = A * W * ω ^ 2 + B * ω := by linear_combination h3
    refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
    · rw [hW_def, hd, zpow_zero] at e3
      right; right; linear_combination e3
    · rw [hWm, hd, zpow_one] at e3
      right; right; linear_combination e3 + A * hω3
    · rw [hWm, hd, zpow_ofNat] at e3
      right; right; linear_combination e3 + A * ω * hω3


-- created on 2018-11-15
