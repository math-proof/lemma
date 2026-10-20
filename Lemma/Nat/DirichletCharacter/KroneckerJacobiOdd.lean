import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.KroneckerJacobiOdd
open MetaMathlibExt


/--
[kroneckerSym_mul_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/KroneckerJacobiOdd.lean)
-/
@[path]
private lemma kroneckerSym_mul_of_odd_eq
  {D : ℤ}
  {m n : ℕ}
-- given
  (hm : Odd m)
  (hn : Odd n) :
-- imply
  kroneckerSym D (m * n) = kroneckerSym D m * kroneckerSym D n := by
-- proof
  apply MetaMathlibExt.kroneckerSym_mul_of_odd D m n hm hn

/--
[kroneckerSym_eq_jacobiSym_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/KroneckerJacobiOdd.lean)
-/
@[path]
private lemma kroneckerSym_eq_jacobiSym_of_odd_eq
  {D : ℤ}
  {n : ℕ}
-- given
  (hn : Odd n) :
-- imply
  kroneckerSym D n = jacobiSym D n := by
-- proof
  apply MetaMathlibExt.kroneckerSym_eq_jacobiSym_of_odd D n hn


-- created on 2026-10-20
