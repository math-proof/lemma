import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RefinedEulerianPolynomial
open scoped BigOperators
open MetaMathlibExt


/--
[refinedEulerianPolynomial_palindromic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RefinedEulerianPolynomial.lean)
-/
@[path]
private lemma refinedEulerianPolynomial_palindromic_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  let oddDescentCount : Equiv.Perm (Fin n) → ℕ := by
-- proof
  apply MetaMathlibExt.refinedEulerianPolynomial_palindromic n hn


-- created on 2026-10-20
