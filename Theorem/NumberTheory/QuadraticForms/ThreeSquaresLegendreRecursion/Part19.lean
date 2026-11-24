module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

lemma r3leg_q_scale (c : ℤ) (x : r3legIntVec) :
    r3legQ (r3legScale c x) = c ^ 2 * r3legQ x := by
  simp [r3legQ, r3legScale]
  ring

end MetaMathlibExt
