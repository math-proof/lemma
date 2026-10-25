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
import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part4


namespace MetaMathlibExt

noncomputable def r3leg_binaryLinearEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (a b : ZMod p) (ha : a ≠ 0) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun z := (a * z.1 + b * z.2, z.2)
  invFun z := ((z.1 - b * z.2) / a, z.2)
  left_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [ha]
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [ha]
      ring
    · rfl

noncomputable def r3leg_binarySqrtEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (a b d : ZMod p) (ha : a ≠ 0) :
    r3legBinaryZeros p a b d ≃ r3legSqrtPairs p (b ^ 2 - a * d) :=
  Equiv.subtypeEquiv (r3leg_binaryLinearEquiv a b ha) (fun z => by
    change a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2 = 0 ↔
      (a * z.1 + b * z.2) ^ 2 = (b ^ 2 - a * d) * z.2 ^ 2
    constructor
    · intro h
      linear_combination a * h
    · intro h
      have h' : a * (a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_left ha)

def r3leg_binarySwapEquiv {p : ℕ} (a b d : ZMod p) :
    r3legBinaryZeros p a b d ≃ r3legBinaryZeros p d b a :=
  Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun z => by
    change a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2 = 0 ↔
      d * z.2 ^ 2 + 2 * b * z.2 * z.1 + a * z.1 ^ 2 = 0
    constructor <;> intro h <;> linear_combination h)

end MetaMathlibExt
