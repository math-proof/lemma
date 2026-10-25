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
import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part8


namespace MetaMathlibExt

noncomputable def r3leg_coneSigmaEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    r3legCone p ≃ (Σ t : ZMod p, r3legTwoSq p (-t ^ 2)) where
  toFun w := ⟨w.1.2, ⟨w.1.1, by
    have hw := w.2
    dsimp [r3legQ] at hw
    linear_combination hw⟩⟩
  invFun z := ⟨(z.2.1, z.1), by
    dsimp [r3legQ]
    linear_combination z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def r3leg_isoConeEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    r3legIso p ≃ {w : r3legCone p // (w.1 : r3legModVec p) ≠ 0} where
  toFun w := ⟨⟨w, w.2.2⟩, w.2.1⟩
  invFun w := ⟨w.1, w.2, w.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
