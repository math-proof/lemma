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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part10


namespace MetaMathlibExt

def r3legInc {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p)
    (w : r3legIso p) (y : r3legIntVec) : Prop :=
  r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star (r3legPi hp3 w)) y)

end MetaMathlibExt
