import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Cyclotomic.LehmerMinpolyDegree
open MetaMathlibExt


/--
[natDegree_realCyclotomicPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerMinpolyDegree.lean)
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


-- created on 2026-10-20
