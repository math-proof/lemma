module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

noncomputable def r3legImageRep (p n : ℕ) (π : Quaternion ℤ) :
    Finset r3legIntVec := by
  classical
  exact (r3legRep (p ^ 2 * n)).filter
    (fun y => r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star π) y))

end MetaMathlibExt
