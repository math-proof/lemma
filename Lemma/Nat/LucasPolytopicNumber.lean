import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LucasPolytopicNumber
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[lucasnomial_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean)
-/
@[path]
lemma lucasnomial_eq_zero_of_lt
  {P : LucasParameters}
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  lucasnomial P n k = 0 := by
-- proof
  simp [lucasnomial, Nat.not_le.mpr h]

end MetaMathlibExt

/--
[lucasBracket_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean)
-/
@[path]
lemma lucasBracket_ne_zero
  {P : LucasParameters}
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  lucasBracket P n ≠ 0 :=
-- proof
  P.bracket_ne_zero n hn


namespace MetaMathlibExt

/--
[lucasFactorial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean)
-/
@[path]
lemma lucasFactorial_ne_zero
  {P : LucasParameters}
  {n : ℕ} :
-- imply
  lucasFactorial P n ≠ 0 := by
-- proof
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact lucasBracket_ne_zero P (Nat.succ_ne_zero k)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
