import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions.Part4
open Finset Real Filter Asymptotics DirichletCharacter
open scoped Nat


/--
[dirichletChar_factorsThrough_iff_ker_and_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArithmeticFunctions.lean)
-/
@[path]
lemma dirichletChar_factorsThrough_iff_ker_and_unique
  [CommMonoidWithZero R]
  {m₂ : ℕ}
  [NeZero m₂]
  {χ₂ : DirichletCharacter R m₂}
  {m₁ : ℕ}
-- given
  (h : m₁ ∣ m₂) :
-- imply
  (χ₂.FactorsThrough m₁ ↔ (ZMod.unitsMap h).ker ≤ χ₂.toUnitHom.ker) ∧ (χ₂.FactorsThrough m₁ → ∃! χ₁ : DirichletCharacter R m₁, χ₂ = changeLevel h χ₁) :=
-- proof
  ⟨DirichletCharacter.factorsThrough_iff_ker_unitsMap h, fun hf => hf.existsUnique⟩


-- created on 2026-10-23
