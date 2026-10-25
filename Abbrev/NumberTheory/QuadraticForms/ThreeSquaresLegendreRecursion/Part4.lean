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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part12


namespace MetaMathlibExt

abbrev r3legBinaryZeros (p : ℕ) (a b d : ZMod p) :=
  {z : ZMod p × ZMod p // a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2 = 0}

end MetaMathlibExt
