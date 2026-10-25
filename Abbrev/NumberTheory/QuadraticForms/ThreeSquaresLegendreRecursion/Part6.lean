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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part12


namespace MetaMathlibExt

abbrev r3legPlane (p : ℕ) (x : r3legModVec p) :=
  {w : r3legModVec p // r3legB w x = 0}

abbrev r3legOrthCone (p : ℕ) (x : r3legModVec p) :=
  {w : r3legModVec p // r3legQ w = 0 ∧ r3legB w x = 0}

end MetaMathlibExt
