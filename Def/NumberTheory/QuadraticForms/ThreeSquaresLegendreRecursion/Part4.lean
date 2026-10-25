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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part3


namespace MetaMathlibExt

def r3legQuatDiv (q : Quaternion ℤ) (c : ℤ) : Quaternion ℤ :=
  { re := q.re / c, imI := q.imI / c, imJ := q.imJ / c, imK := q.imK / c }

end MetaMathlibExt
