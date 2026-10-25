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
import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part7


namespace MetaMathlibExt

noncomputable def r3leg_twoSqLinearEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (α β c : ZMod p) (hc : c ≠ 0) (hab : α ^ 2 + β ^ 2 = c) :
    ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun z := (α * z.1 - β * z.2, β * z.1 + α * z.2)
  invFun z := ((α * z.1 + β * z.2) / c, (-β * z.1 + α * z.2) / c)
  left_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [hc]
      linear_combination z.1 * hab
    · dsimp
      field_simp [hc]
      linear_combination z.2 * hab
  right_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [hc]
      linear_combination z.1 * hab
    · dsimp
      field_simp [hc]
      linear_combination z.2 * hab

noncomputable def r3leg_twoSqEquivOne {p : ℕ} [Fact (Nat.Prime p)]
    (c : ZMod p) (hc : c ≠ 0) : r3legTwoSq p 1 ≃ r3legTwoSq p c := by
  let h := ZMod.sq_add_sq p c
  let α := Classical.choose h
  let β := Classical.choose (Classical.choose_spec h)
  have hab : α ^ 2 + β ^ 2 = c := Classical.choose_spec (Classical.choose_spec h)
  exact Equiv.subtypeEquiv (r3leg_twoSqLinearEquiv α β c hc hab) (fun z => by
    change z.1 ^ 2 + z.2 ^ 2 = 1 ↔
      (α * z.1 - β * z.2) ^ 2 + (β * z.1 + α * z.2) ^ 2 = c
    constructor
    · intro hz
      calc
        (α * z.1 - β * z.2) ^ 2 + (β * z.1 + α * z.2) ^ 2 =
            (α ^ 2 + β ^ 2) * (z.1 ^ 2 + z.2 ^ 2) := by ring
        _ = c * (z.1 ^ 2 + z.2 ^ 2) := by rw [hab]
        _ = c := by rw [hz, mul_one]
    · intro hz
      have hmul : c * (z.1 ^ 2 + z.2 ^ 2) = c * 1 := by
        calc
          c * (z.1 ^ 2 + z.2 ^ 2) =
              (α * z.1 - β * z.2) ^ 2 + (β * z.1 + α * z.2) ^ 2 := by
            rw [← hab]
            ring
          _ = c := hz
          _ = c * 1 := by ring
      exact mul_left_cancel₀ hc hmul)

noncomputable def r3leg_twoSqSigmaEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    (Σ c : ZMod p, r3legTwoSq p c) ≃ ZMod p × ZMod p where
  toFun z := z.2
  invFun z := ⟨z.1 ^ 2 + z.2 ^ 2, ⟨z, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨c, ⟨z, hz⟩⟩
    subst c
    rfl
  right_inv _ := rfl

end MetaMathlibExt
