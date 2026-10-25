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


namespace MetaMathlibExt

/-! # Legendre-symbol recursion for sums of three squares

This file proves the prime-power recursion for `Nat.threeSquareRepresentationCount` in terms of a
Legendre symbol and a geometric sum.
-/

abbrev r3legIntVec := (ℤ × ℤ) × ℤ

abbrev r3legModVec (p : ℕ) := (ZMod p × ZMod p) × ZMod p

end MetaMathlibExt
