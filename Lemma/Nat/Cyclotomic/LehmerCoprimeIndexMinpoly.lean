import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Cyclotomic.LehmerCoprimeIndexMinpoly
open MetaMathlibExt


/--
[realCyclotomicPolynomial_eq_minpoly_two_cos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerCoprimeIndexMinpoly.lean)
-/
@[path]
private lemma realCyclotomicPolynomial_eq_minpoly_two_cos_eq
  {n k : ℕ}
-- given
  (hn : 2 < n)
  (hcop : Nat.Coprime k n) :
-- imply
  realCyclotomicPolynomial n =
    minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ) : ℂ)) := by
-- proof
  apply MetaMathlibExt.realCyclotomicPolynomial_eq_minpoly_two_cos hn hcop

/--
[realCyclotomicPolynomial_eq_minpoly_two_cos_of_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerCoprimeIndexMinpoly.lean)
-/
@[path]
private lemma realCyclotomicPolynomial_eq_minpoly_two_cos_of_coprime_eq
  {n k : ℕ}
-- given
  (hn : 2 < n)
  (hk1 : 1 ≤ k)
  (hkn : k ≤ n)
  (hcop : Nat.Coprime k n) :
-- imply
  realCyclotomicPolynomial n =
    minpoly ℤ (((2 * Real.cos (2 * (k : ℝ) * Real.pi / (n : ℝ)) : ℝ) : ℂ)) := by
-- proof
  apply MetaMathlibExt.realCyclotomicPolynomial_eq_minpoly_two_cos_of_coprime hn hk1 hkn hcop


-- created on 2026-10-20
