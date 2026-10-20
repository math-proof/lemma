import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticCharacterAux
open MetaMathlibExt


/--
[IsFundamentalDiscriminant.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
private lemma IsFundamentalDiscriminant_ne_zero_eq
  {D : ℤ}
-- given
  (hD : IsFundamentalDiscriminant D) :
-- imply
  D ≠ 0 := by
-- proof
  apply MetaMathlibExt.IsFundamentalDiscriminant.ne_zero D hD

/--
[IsFundamentalDiscriminant.natAbs_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
private lemma IsFundamentalDiscriminant_natAbs_pos_eq
  {D : ℤ}
-- given
  (hD : IsFundamentalDiscriminant D) :
-- imply
  0 < D.natAbs := by
-- proof
  apply MetaMathlibExt.IsFundamentalDiscriminant.natAbs_pos D hD

/--
[kroneckerSym_one_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
private lemma kroneckerSym_one_left_eq
  {n : ℕ} :
-- imply
  kroneckerSym 1 n = 1 := by
-- proof
  apply MetaMathlibExt.kroneckerSym_one_left n

/--
[kroneckerSym_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
private lemma kroneckerSym_mul_eq
  {D : ℤ}
  {m n : ℕ}
-- given
  (hD : D ≠ -1) :
-- imply
  kroneckerSym D (m * n) =
    kroneckerSym D m * kroneckerSym D n := by
-- proof
  apply MetaMathlibExt.kroneckerSym_mul D hD m n

/--
[kroneckerSym_eq_jacobiSym_of_prime_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticCharacterAux.lean)
-/
@[path]
private lemma kroneckerSym_eq_jacobiSym_of_prime_ne_two_eq
  {D : ℤ}
  {p : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2) :
-- imply
  kroneckerSym D p = jacobiSym D p := by
-- proof
  apply MetaMathlibExt.kroneckerSym_eq_jacobiSym_of_prime_ne_two D p hp hp2


-- created on 2026-10-20
