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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part17


namespace MetaMathlibExt

lemma r3leg_orthCone_card {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legModVec p) (hx : x ≠ 0) :
    (Fintype.card (r3legOrthCone p x) : ℤ) =
      (p : ℤ) + ((p : ℤ) - 1) * quadraticChar (ZMod p) (-r3legQ x) := by
  by_cases h₃ : x.2 = 0
  · by_cases h₁ : x.1.1 = 0
    · have h₂ : x.1.2 ≠ 0 := by
        intro h₂
        apply hx
        apply Prod.ext
        · exact Prod.ext h₁ h₂
        · exact h₃
      let x' := r3legRot (r3legRot x)
      have hx' : x'.2 ≠ 0 := by simpa [x', r3legRot] using h₂
      have hcard := r3leg_orthCone_card_of_third_ne_zero hp3 x' hx'
      have hc₁ := Fintype.card_congr (r3leg_rotOrthEquiv x)
      have hc₂ := Fintype.card_congr (r3leg_rotOrthEquiv (r3legRot x))
      have hq : r3legQ x' = r3legQ x := by
        dsimp [x']
        rw [r3leg_q_rot, r3leg_q_rot]
      rw [hq] at hcard
      have hc : Fintype.card (r3legOrthCone p x) =
          Fintype.card (r3legOrthCone p x') := hc₁.trans hc₂
      have hc' : (Fintype.card (r3legOrthCone p x) : ℤ) =
          Fintype.card (r3legOrthCone p x') := by exact_mod_cast hc
      rw [hc']
      exact hcard
    · let x' := r3legRot x
      have hx' : x'.2 ≠ 0 := by simpa [x', r3legRot] using h₁
      have hcard := r3leg_orthCone_card_of_third_ne_zero hp3 x' hx'
      have hc := Fintype.card_congr (r3leg_rotOrthEquiv x)
      have hq : r3legQ x' = r3legQ x := by
        dsimp [x']
        rw [r3leg_q_rot]
      rw [hq] at hcard
      have hc' : (Fintype.card (r3legOrthCone p x) : ℤ) =
          Fintype.card (r3legOrthCone p x') := by exact_mod_cast hc
      rw [hc']
      exact hcard
  · exact r3leg_orthCone_card_of_third_ne_zero hp3 x h₃

end MetaMathlibExt
