module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def r3legEpsI : Quaternion ℤ :=
  { re := 1, imI := -1, imJ := 0, imK := 0 }

def r3legEpsJ : Quaternion ℤ :=
  { re := 1, imI := 0, imJ := -1, imK := 0 }

def r3legEpsK : Quaternion ℤ :=
  { re := 1, imI := 0, imJ := 0, imK := -1 }

end MetaMathlibExt
