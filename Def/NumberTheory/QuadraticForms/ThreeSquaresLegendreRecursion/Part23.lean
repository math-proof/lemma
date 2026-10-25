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
import Instance.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part2


namespace MetaMathlibExt

def r3leg_incRepImageEquiv {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) :
    {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y} ≃
      (r3legImageRep p n (r3legPi hp3 w) : Type) where
  toFun y := ⟨y.1, r3leg_mem_imageRep.mpr
    ⟨r3leg_mem_rep.mp y.1.2, y.2⟩⟩
  invFun y := ⟨⟨y, r3leg_mem_rep.mpr (r3leg_mem_imageRep.mp y.2).1⟩,
    (r3leg_mem_imageRep.mp y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
