import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.Quadratic
open MetaMathlibExt


/--
[kroneckerSym_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
private lemma kroneckerSym_zero_eq
  {D : ℤ} :
-- imply
  kroneckerSym D 0 = if D.natAbs = 1 then 1 else 0 := by
-- proof
  apply MetaMathlibExt.kroneckerSym_zero D

/--
[kroneckerSym_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
private lemma kroneckerSym_one_eq
  {D : ℤ} :
-- imply
  kroneckerSym D 1 = 1 := by
-- proof
  apply MetaMathlibExt.kroneckerSym_one D

/--
[kroneckerAtPrime_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
private lemma kroneckerAtPrime_two_eq
  {D : ℤ} :
-- imply
  kroneckerAtPrime D 2 = kroneckerAtTwo D := by
-- proof
  apply MetaMathlibExt.kroneckerAtPrime_two D

/--
[kroneckerSym_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
private lemma kroneckerSym_two_eq
  {D : ℤ} :
-- imply
  kroneckerSym D 2 = kroneckerAtTwo D := by
-- proof
  apply MetaMathlibExt.kroneckerSym_two D

/--
[kroneckerSym_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Quadratic.lean)
-/
@[path]
private lemma kroneckerSym_prime_eq
  {D : ℤ}
  {p : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  kroneckerSym D p = kroneckerAtPrime D p := by
-- proof
  apply MetaMathlibExt.kroneckerSym_prime D p hp


-- created on 2026-10-20
