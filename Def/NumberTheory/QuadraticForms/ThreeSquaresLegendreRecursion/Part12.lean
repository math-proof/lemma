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
import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part3


namespace MetaMathlibExt

noncomputable def r3leg_sqrtPairEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (Δ : ZMod p) :
    r3legSqrtPairs p Δ ≃ Option ((ZMod p)ˣ × r3legSqrts p Δ) where
  toFun z := if ht : z.1.2 = 0 then none else
    some (Units.mk0 z.1.2 ht, ⟨z.1.1 / z.1.2, by
      field_simp [ht]
      simpa [mul_comm] using z.2⟩)
  invFun z := match z with
    | none => ⟨(0, 0), by simp⟩
    | some z => ⟨(z.2 * z.1, z.1), by
        rw [mul_pow, z.2.property]⟩
  left_inv z := by
    dsimp
    split_ifs with ht
    · apply Subtype.ext
      apply Prod.ext
      · have hz : z.1.1 = 0 := by
          apply sq_eq_zero_iff.mp
          simpa [ht] using z.2
        exact hz.symm
      · exact ht.symm
    · apply Subtype.ext
      apply Prod.ext
      · simp [ht]
      · rfl
  right_inv z := by
    cases z with
    | none => simp
    | some z =>
        have ht : (z.1 : ZMod p) ≠ 0 := Units.ne_zero z.1
        simp [ht]

end MetaMathlibExt
