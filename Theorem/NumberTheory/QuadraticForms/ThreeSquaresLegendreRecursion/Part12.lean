/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part14


namespace MetaMathlibExt

lemma r3leg_binary_card {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (a b d : ZMod p) (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0) :
    (Fintype.card (r3legBinaryZeros p a b d) : ℤ) =
      1 + ((p : ℤ) - 1) *
        (1 + quadraticChar (ZMod p) (b ^ 2 - a * d)) := by
  by_cases ha : a = 0
  · subst a
    by_cases hd : d = 0
    · subst d
      have hb : b ≠ 0 := by tauto
      have h2b : (2 : ZMod p) * b ≠ 0 :=
        mul_ne_zero (by exact_mod_cast r3leg_two_ne_zero hp3) hb
      let e : r3legBinaryZeros p 0 b 0 ≃ r3legZeroProd p :=
        Equiv.subtypeEquiv (Equiv.refl _) (fun z => by
          change 0 * z.1 ^ 2 + 2 * b * z.1 * z.2 + 0 * z.2 ^ 2 = 0 ↔
            z.1 * z.2 = 0
          constructor
          · intro h
            have h' : ((2 : ZMod p) * b) * (z.1 * z.2) = 0 := by
              linear_combination h
            exact (mul_eq_zero.mp h').resolve_left h2b
          · intro h
            linear_combination ((2 : ZMod p) * b) * h)
      rw [Fintype.card_congr e, r3leg_zeroProd_card hp3]
      simp only [zero_mul, sub_zero]
      rw [quadraticChar_sq_one' hb]
      ring
    · have hswap := r3leg_binary_card_of_left_ne_zero hp3 d b 0 hd
      rw [Fintype.card_congr (r3leg_binarySwapEquiv 0 b d)]
      simpa [mul_comm] using hswap
  · exact r3leg_binary_card_of_left_ne_zero hp3 a b d ha

end MetaMathlibExt
