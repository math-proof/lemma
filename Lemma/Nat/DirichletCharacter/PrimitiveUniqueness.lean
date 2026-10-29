import Mathlib
import Initialize.Tactic.Attr.Basic


namespace DirichletCharacter

/--
[conductor_eq_of_isPrimitive_changeLevel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean)
-/
@[path]
lemma conductor_eq_of_isPrimitive_changeLevel
  [CommMonoidWithZero R]
  {n : ℕ} [NeZero n]
  {d : ℕ}
  {χ' : DirichletCharacter R d}
  (χ : DirichletCharacter R n)
-- given
  (hprim : χ'.IsPrimitive)
  (hd : d ∣ n)
  (h : changeLevel hd χ' = χ) :
-- imply
  d = χ.conductor := by
-- proof
  have hprim' : χ'.conductor = d := hprim
  have hcond := conductor_changeLevel χ' hd
  rw [h] at hcond
  exact hprim'.symm.trans hcond.symm

end DirichletCharacter

namespace DirichletCharacter

/--
[eq_primitiveCharacter_of_changeLevel_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean)
-/
@[path]
lemma eq_primitiveCharacter_of_changeLevel_eq
  [CommMonoidWithZero R]
  {n : ℕ} [NeZero n]
  {d : ℕ}
  {χ' : DirichletCharacter R d}
  (χ : DirichletCharacter R n)
-- given
  (hlev : d = χ.conductor)
  (hd : d ∣ n)
  (h : changeLevel hd χ' = χ) :
-- imply
  hlev ▸ χ' = χ.primitiveCharacter := by
-- proof
  subst hlev
  have hcanon : changeLevel hd χ.primitiveCharacter = χ :=
    changeLevel_primitiveCharacter χ
  have heq : changeLevel hd χ' = changeLevel hd χ.primitiveCharacter := by
    rw [h, hcanon]
  exact changeLevel_injective hd heq

end DirichletCharacter

namespace DirichletCharacter

/--
[primitiveCharacter_isPrimitive_and_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean)
-/
@[path]
lemma primitiveCharacter_isPrimitive_and_unique
  [CommMonoidWithZero R]
  {n : ℕ} [NeZero n]
  {χ : DirichletCharacter R n} :
-- imply
  χ.primitiveCharacter.IsPrimitive ∧
      changeLevel (conductor_dvd_level χ) χ.primitiveCharacter = χ ∧
      ∀ (d : ℕ) (χ' : DirichletCharacter R d), χ'.IsPrimitive →
        ∀ (hd : d ∣ n), changeLevel hd χ' = χ →
          ∃ (hlev : d = χ.conductor), hlev ▸ χ' = χ.primitiveCharacter := by
-- proof
  refine ⟨primitiveCharacter_isPrimitive χ, changeLevel_primitiveCharacter χ,
    fun d χ' hprim hd h => ?_⟩
  have hlev := conductor_eq_of_isPrimitive_changeLevel χ hprim hd h
  exact ⟨hlev, eq_primitiveCharacter_of_changeLevel_eq χ hlev hd h⟩

end DirichletCharacter


-- created on 2026-10-20
-- updated on 2026-10-28
