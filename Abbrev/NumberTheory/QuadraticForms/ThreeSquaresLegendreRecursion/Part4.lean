module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

abbrev r3legBinaryZeros (p : ℕ) (a b d : ZMod p) :=
  {z : ZMod p × ZMod p // a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2 = 0}

end MetaMathlibExt
