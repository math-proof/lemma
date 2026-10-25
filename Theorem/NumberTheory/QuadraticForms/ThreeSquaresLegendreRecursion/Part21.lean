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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part23


namespace MetaMathlibExt

lemma r3leg_incRep_card {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) :
    Fintype.card {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y} =
      Nat.threeSquareRepresentationCount n := by
  rw [Fintype.card_congr (r3leg_incRepImageEquiv hp3 w), Fintype.card_coe,
    r3leg_imageRep_card _ (r3legPi_norm hp3 w)]

end MetaMathlibExt
