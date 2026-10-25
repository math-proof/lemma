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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part8


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
