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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part7


namespace MetaMathlibExt

def r3legVecDvd (c : ℤ) (x : r3legIntVec) : Prop :=
  c ∣ x.1.1 ∧ c ∣ x.1.2 ∧ c ∣ x.2

def r3legVecDiv (x : r3legIntVec) (c : ℤ) : r3legIntVec :=
  ((x.1.1 / c, x.1.2 / c), x.2 / c)

end MetaMathlibExt
