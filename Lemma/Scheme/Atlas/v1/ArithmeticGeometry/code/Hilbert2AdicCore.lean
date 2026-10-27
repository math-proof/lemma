import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore.Part2
open PadicInt HilbertSymbol


/--
[toZModPow_unit_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean)
-/
@[path]
lemma toZModPow_unit_coe
  {n : ℕ}
  {u : ℤ_[2]ˣ} :
-- imply
  (toZModPow_unit n u : ZMod (2 ^ n)) = toZModPow n (↑u) :=
-- proof
  IsUnit.unit_spec _

/--
[formula_one_one_verified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean)
-/
@[path]
lemma formula_one_one_verified
-- imply
  ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ, hasPrimSolMod8_one_dec u₀ v₀ ↔ hilbert2Adic_formula u₀ v₀ 0 0 = 1 := by
-- proof
  native_decide

/--
[formula_two_one_verified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean)
-/
@[path]
lemma formula_two_one_verified
-- imply
  ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ, hasPrimSolMod8_two_dec u₀ v₀ ↔ hilbert2Adic_formula u₀ v₀ 1 0 = 1 := by
-- proof
  native_decide

/--
[formula_one_two_verified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean)
-/
@[path]
lemma formula_one_two_verified
-- imply
  ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ, hasPrimSolMod8_two_dec v₀ u₀ ↔ hilbert2Adic_formula u₀ v₀ 0 1 = 1 := by
-- proof
  native_decide

/--
[formula_bilinear_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean)
-/
@[path]
lemma formula_bilinear_identity
-- imply
  ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ, hilbert2Adic_formula u₀ v₀ 1 1 = hilbert2Adic_formula (1 : (ZMod (2 ^ 3))ˣ) u₀ 1 0 * hilbert2Adic_formula (-1 : (ZMod (2 ^ 3))ˣ) (1 : (ZMod (2 ^ 3))ˣ) 0 1 * hilbert2Adic_formula u₀ v₀ 1 0 := by
-- proof
native_decide

/--
[formula_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean)
-/
@[path]
lemma formula_eq_one_or_neg_one
  {u₀ v₀ : (ZMod (2 ^ 3))ˣ}
  {α β : ℕ} :
-- imply
  hilbert2Adic_formula u₀ v₀ α β = 1 ∨ hilbert2Adic_formula u₀ v₀ α β = -1 := by
-- proof
  unfold hilbert2Adic_formula
  exact neg_one_pow_eq_or ℤ _

/--
[formula_mul_left_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean)
-/
@[path]
lemma formula_mul_left_core
-- imply
  ∀ (u₁ u₂ w : (ZMod (2 ^ 3))ˣ) (α₁ α₂ γ : Fin 2), hilbert2Adic_formula (u₁ * u₂) w ((α₁ : ℕ) + (α₂ : ℕ)) (γ : ℕ) = hilbert2Adic_formula u₁ w (α₁ : ℕ) (γ : ℕ) * hilbert2Adic_formula u₂ w (α₂ : ℕ) (γ : ℕ) := by
-- proof
native_decide


-- created on 2026-10-23
