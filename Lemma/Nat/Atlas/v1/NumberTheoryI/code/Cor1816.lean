import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Cor1816.Part2
open DirichletCharacter PrimCharDvd


/--
[ext'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean)
-/
@[path]
private lemma ext'_eq
  [CommMonoidWithZero R]
  {m : ℕ}
  {p q : PrimCharDvd R m}
-- given
  (hd : p.d = q.d)
  (hχ : hd ▸ p.χ = q.χ) :
-- imply
  p = q := by
-- proof
  apply PrimCharDvd.ext' hd hχ

/--
[changeLevel_cast_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean)
-/
@[path]
private lemma changeLevel_cast_eq_eq
  [CommMonoidWithZero R]
  {m d₁ d₂ : ℕ}
  {ψ : DirichletCharacter R d₁}
-- given
  (heq : d₁ = d₂)
  (hd₂ : d₂ ∣ m) :
-- imply
  changeLevel hd₂ (heq ▸ ψ) = changeLevel (show d₁ ∣ m from heq ▸ hd₂) ψ := by
-- proof
  apply DirichletCharacter.changeLevel_cast_eq heq hd₂ ψ

/--
[fromPrimCharDvd_toPrimCharDvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean)
-/
@[path]
private lemma fromPrimCharDvd_toPrimCharDvd_eq
  [CommMonoidWithZero R]
  {m : ℕ}
  {χ : DirichletCharacter R m} :
-- imply
  fromPrimCharDvd (toPrimCharDvd χ) = χ := by
-- proof
  apply DirichletCharacter.fromPrimCharDvd_toPrimCharDvd χ

/--
[conductor_changeLevel_of_isPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean)
-/
@[path]
private lemma conductor_changeLevel_of_isPrimitive_eq
  [CommMonoidWithZero R]
  {m d : ℕ}
  {ψ : DirichletCharacter R d}
-- given
  (hm : m ≠ 0)
  (hd : d ∣ m)
  (hprim : ψ.IsPrimitive) :
-- imply
  (changeLevel hd ψ).conductor = d := by
-- proof
  apply DirichletCharacter.conductor_changeLevel_of_isPrimitive hm hd ψ hprim

/--
[toPrimCharDvd_fromPrimCharDvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean)
-/
@[path]
private lemma toPrimCharDvd_fromPrimCharDvd_eq
  [CommMonoidWithZero R]
  {m : ℕ}
  {p : PrimCharDvd R m}
-- given
  (hm : m ≠ 0) :
-- imply
  toPrimCharDvd (fromPrimCharDvd p) = p := by
-- proof
  apply DirichletCharacter.toPrimCharDvd_fromPrimCharDvd hm p


-- created on 2026-10-23
