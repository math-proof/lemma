import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LucasPolytopicNumber
open scoped BigOperators
open MetaMathlibExt


/--
[lucasBracket_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean)
-/
@[path]
private lemma lucasBracket_ne_zero_eq
  {P : LucasParameters}
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  lucasBracket P n ≠ 0 := by
-- proof
  apply MetaMathlibExt.lucasBracket_ne_zero P hn

/--
[lucasFactorial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean)
-/
@[path]
private lemma lucasFactorial_ne_zero_eq
  {P : LucasParameters}
  {n : ℕ} :
-- imply
  lucasFactorial P n ≠ 0 := by
-- proof
  apply MetaMathlibExt.lucasFactorial_ne_zero P n

/--
[lucasnomial_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean)
-/
@[path]
private lemma lucasnomial_eq_zero_of_lt_eq
  {P : LucasParameters}
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  lucasnomial P n k = 0 := by
-- proof
  apply MetaMathlibExt.lucasnomial_eq_zero_of_lt P h


-- created on 2026-10-20
