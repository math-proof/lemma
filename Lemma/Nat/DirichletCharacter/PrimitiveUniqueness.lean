import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.PrimitiveUniqueness
open DirichletCharacter


/--
[conductor_eq_of_isPrimitive_changeLevel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean)
-/
@[path]
private lemma conductor_eq_of_isPrimitive_changeLevel_eq
  [CommMonoidWithZero R]
  {n : ℕ} [NeZero n]
  {d : ℕ}
  {χ' : DirichletCharacter R d}
  {χ : DirichletCharacter R n}
-- given
  (hprim : χ'.IsPrimitive)
  (hd : d ∣ n)
  (h : changeLevel hd χ' = χ) :
-- imply
  d = χ.conductor := by
-- proof
  apply DirichletCharacter.conductor_eq_of_isPrimitive_changeLevel χ hprim hd h

/--
[eq_primitiveCharacter_of_changeLevel_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean)
-/
@[path]
private lemma eq_primitiveCharacter_of_changeLevel_eq_eq
  [CommMonoidWithZero R]
  {n : ℕ} [NeZero n]
  {d : ℕ}
  {χ' : DirichletCharacter R d}
  {χ : DirichletCharacter R n}
-- given
  (hlev : d = χ.conductor)
  (hd : d ∣ n)
  (h : changeLevel hd χ' = χ) :
-- imply
  hlev ▸ χ' = χ.primitiveCharacter := by
-- proof
  apply DirichletCharacter.eq_primitiveCharacter_of_changeLevel_eq χ hlev hd h

/--
[primitiveCharacter_isPrimitive_and_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean)
-/
@[path]
private lemma primitiveCharacter_isPrimitive_and_unique_eq
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
  apply DirichletCharacter.primitiveCharacter_isPrimitive_and_unique χ


-- created on 2026-10-20
