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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part2


namespace MetaMathlibExt

def r3legEpsI : Quaternion ℤ :=
  { re := 1, imI := -1, imJ := 0, imK := 0 }

def r3legEpsJ : Quaternion ℤ :=
  { re := 1, imI := 0, imJ := -1, imK := 0 }

def r3legEpsK : Quaternion ℤ :=
  { re := 1, imI := 0, imJ := 0, imK := -1 }

end MetaMathlibExt
