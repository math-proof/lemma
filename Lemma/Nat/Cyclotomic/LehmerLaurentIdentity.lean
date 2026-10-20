import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Cyclotomic.LehmerLaurentIdentity
open MetaMathlibExt


/--
[natDegree_realCyclotomicPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma natDegree_realCyclotomicPolynomial_eq
  {n : ℕ}
-- given
  (hn : 2 < n) :
-- imply
  Even n.totient ∧ (realCyclotomicPolynomial n).natDegree = n.totient / 2 := by
-- proof
  apply MetaMathlibExt.natDegree_realCyclotomicPolynomial n hn

/--
[lehmer_cyclotomic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma lehmer_cyclotomic_identity_eq
  {n : ℕ}
-- given
  (hn : 2 < n) :
-- imply
  LaurentPolynomial.T (↑(n.totient / 2)) *
    Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
    (realCyclotomicPolynomial n) =
    Polynomial.toLaurent (Polynomial.cyclotomic n ℤ) := by
-- proof
  apply MetaMathlibExt.lehmer_cyclotomic_identity n hn


-- created on 2026-10-20
