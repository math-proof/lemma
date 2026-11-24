module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

abbrev r3legSqrtPairs (p : ℕ) (Δ : ZMod p) :=
  {z : ZMod p × ZMod p // z.1 ^ 2 = Δ * z.2 ^ 2}

abbrev r3legSqrts (p : ℕ) (Δ : ZMod p) :=
  {z : ZMod p // z ^ 2 = Δ}

end MetaMathlibExt
