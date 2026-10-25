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
import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part5


namespace MetaMathlibExt

noncomputable def r3leg_zeroProdEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    r3legZeroProd p ≃ (ZMod p ⊕ (ZMod p)ˣ) where
  toFun z := if ht : z.1.2 = 0 then Sum.inl z.1.1 else Sum.inr (Units.mk0 z.1.2 ht)
  invFun z := match z with
    | Sum.inl s => ⟨(s, 0), by simp⟩
    | Sum.inr t => ⟨(0, t), by simp⟩
  left_inv z := by
    dsimp
    split_ifs with ht
    · apply Subtype.ext
      exact Prod.ext rfl ht.symm
    · apply Subtype.ext
      apply Prod.ext
      · have hs : z.1.1 = 0 :=
          (mul_eq_zero.mp z.2).resolve_right ht
        exact hs.symm
      · rfl
  right_inv z := by
    cases z with
    | inl s => simp
    | inr t =>
        have ht : (t : ZMod p) ≠ 0 := Units.ne_zero t
        simp [ht]

end MetaMathlibExt
