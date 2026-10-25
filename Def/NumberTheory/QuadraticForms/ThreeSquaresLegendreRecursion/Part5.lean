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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part4


namespace MetaMathlibExt

def r3legQuatBmod (q : Quaternion ℤ) (m : ℕ) : Quaternion ℤ :=
  { re := q.re.bmod m, imI := q.imI.bmod m,
    imJ := q.imJ.bmod m, imK := q.imK.bmod m }

end MetaMathlibExt
