import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.Cohn
open scoped BigOperators
open MetaMathlibExt


/--
[cohn_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/Cohn.lean)
-/
@[path]
private lemma cohn_criterion_eq
  {b p : ℕ}
-- given
  (hp : Nat.Prime p)
  (hb : 2 ≤ b) :
-- imply
  Irreducible (∑ i ∈ Finset.range (Nat.digits b p).length,
    Polynomial.monomial i ((Nat.digits b p)[i]! : ℤ) : Polynomial ℤ) := by
-- proof
  apply MetaMathlibExt.cohn_criterion b p hp hb


-- created on 2026-10-20
