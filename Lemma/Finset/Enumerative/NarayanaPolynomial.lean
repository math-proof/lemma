import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.NarayanaPolynomial
open MetaMathlibExt


/--
[narayanaPolynomialCoeff_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaPolynomial.lean)
-/
@[path]
private lemma narayanaPolynomialCoeff_succ_succ_eq
  {n k : ℕ} :
-- imply
  narayanaPolynomialCoeff (n + 1) (k + 1) =
    narayana ⟨n + 1, Nat.succ_pos n⟩ ⟨k + 1, Nat.succ_pos k⟩ := by
-- proof
  apply MetaMathlibExt.narayanaPolynomialCoeff_succ_succ n k


-- created on 2026-10-20
