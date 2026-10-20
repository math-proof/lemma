/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean -/

import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
Uniqueness of the primitive Dirichlet character inducing a given character.

A primitive character at level `d` inducing `χ` at level `n` must live at
the conductor level, and transported to that level it coincides with the
canonical primitive character `χ.primitiveCharacter`.
-/

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]

/-- The level of a primitive character inducing `χ` is the conductor. -/
theorem conductor_eq_of_isPrimitive_changeLevel {d : ℕ}
    {χ' : DirichletCharacter R d} (χ : DirichletCharacter R n)
    (hprim : χ'.IsPrimitive) (hd : d ∣ n)
    (h : changeLevel hd χ' = χ) : d = χ.conductor := by
  have hprim' : χ'.conductor = d := hprim
  have hcond := conductor_changeLevel χ' hd
  rw [h] at hcond
  exact hprim'.symm.trans hcond.symm

/-- An inducer of `χ`, transported to the conductor level, is the canonical
primitive character. -/
theorem eq_primitiveCharacter_of_changeLevel_eq {d : ℕ}
    {χ' : DirichletCharacter R d} (χ : DirichletCharacter R n)
    (hlev : d = χ.conductor) (hd : d ∣ n)
    (h : changeLevel hd χ' = χ) :
    hlev ▸ χ' = χ.primitiveCharacter := by
  subst hlev
  have hcanon : changeLevel hd χ.primitiveCharacter = χ :=
    changeLevel_primitiveCharacter χ
  have heq : changeLevel hd χ' = changeLevel hd χ.primitiveCharacter := by
    rw [h, hcanon]
  exact changeLevel_injective hd heq

/-- The canonical primitive character is primitive, induces `χ`, and every
primitive inducer of `χ` agrees with it after transport to the conductor. -/
theorem primitiveCharacter_isPrimitive_and_unique (χ : DirichletCharacter R n) :
    χ.primitiveCharacter.IsPrimitive ∧
      changeLevel (conductor_dvd_level χ) χ.primitiveCharacter = χ ∧
      ∀ (d : ℕ) (χ' : DirichletCharacter R d), χ'.IsPrimitive →
        ∀ (hd : d ∣ n), changeLevel hd χ' = χ →
          ∃ (hlev : d = χ.conductor), hlev ▸ χ' = χ.primitiveCharacter := by
  refine ⟨primitiveCharacter_isPrimitive χ, changeLevel_primitiveCharacter χ,
    fun d χ' hprim hd h => ?_⟩
  have hlev := conductor_eq_of_isPrimitive_changeLevel χ hprim hd h
  exact ⟨hlev, eq_primitiveCharacter_of_changeLevel_eq χ hlev hd h⟩

end DirichletCharacter
