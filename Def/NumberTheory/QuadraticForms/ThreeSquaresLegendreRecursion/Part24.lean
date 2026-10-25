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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part21


namespace MetaMathlibExt

def r3leg_incidenceSwap {p n : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Σ w : r3legIso p,
      {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y}) ≃
    (Σ y : r3legRepType (p ^ 2 * n),
      {w : r3legIso p // r3legInc hp3 w y}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
