module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

abbrev r3legPlane (p : ℕ) (x : r3legModVec p) :=
  {w : r3legModVec p // r3legB w x = 0}

abbrev r3legOrthCone (p : ℕ) (x : r3legModVec p) :=
  {w : r3legModVec p // r3legQ w = 0 ∧ r3legB w x = 0}

end MetaMathlibExt
