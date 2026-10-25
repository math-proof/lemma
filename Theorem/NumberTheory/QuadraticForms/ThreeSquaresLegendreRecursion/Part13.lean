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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part15


namespace MetaMathlibExt

lemma r3leg_orthCone_card_of_third_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legModVec p) (hx : x.2 ≠ 0) :
    (Fintype.card (r3legOrthCone p x) : ℤ) =
      (p : ℤ) + ((p : ℤ) - 1) * quadraticChar (ZMod p) (-r3legQ x) := by
  let a := x.1.1 ^ 2 + x.2 ^ 2
  let b := x.1.1 * x.1.2
  let d := x.1.2 ^ 2 + x.2 ^ 2
  have hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0 := by
    by_cases h₁ : x.1.1 = 0
    · left
      simp [a, h₁, hx]
    · by_cases h₂ : x.1.2 = 0
      · right; right
        simp [d, h₂, hx]
      · right; left
        exact mul_ne_zero h₁ h₂
  have hcard := r3leg_binary_card hp3 a b d hcoeff
  rw [Fintype.card_congr (r3leg_binaryOrthEquiv x hx)] at hcard
  have hdisc : b ^ 2 - a * d = x.2 ^ 2 * (-r3legQ x) := by
    dsimp [a, b, d, r3legQ]
    ring
  have hchar : quadraticChar (ZMod p) (b ^ 2 - a * d) =
      quadraticChar (ZMod p) (-r3legQ x) := by
    rw [hdisc, map_mul, quadraticChar_sq_one' hx, one_mul]
  rw [hchar] at hcard
  linear_combination hcard

end MetaMathlibExt
