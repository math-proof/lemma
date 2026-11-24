module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

lemma r3leg_scale_vecDiv {c : ℤ} {x : r3legIntVec}
    (h : r3legVecDvd c x) : r3legScale c (r3legVecDiv x c) = x := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  apply Prod.ext
  · apply Prod.ext
    · exact Int.mul_ediv_cancel' h₁
    · exact Int.mul_ediv_cancel' h₂
  · exact Int.mul_ediv_cancel' h₃

end MetaMathlibExt
