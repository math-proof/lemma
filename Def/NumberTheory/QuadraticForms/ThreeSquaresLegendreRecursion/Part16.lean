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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part13


namespace MetaMathlibExt

def r3legRot {R : Type*} : ((R × R) × R) ≃ ((R × R) × R) where
  toFun x := ((x.1.2, x.2), x.1.1)
  invFun x := ((x.2, x.1.1), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
