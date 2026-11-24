module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def r3legVecDvd (c : ℤ) (x : r3legIntVec) : Prop :=
  c ∣ x.1.1 ∧ c ∣ x.1.2 ∧ c ∣ x.2

def r3legVecDiv (x : r3legIntVec) (c : ℤ) : r3legIntVec :=
  ((x.1.1 / c, x.1.2 / c), x.2 / c)

end MetaMathlibExt
