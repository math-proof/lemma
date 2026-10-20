import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.StirlingBellPolynomialConnection
open scoped BigOperators
open MetaMathlibExt


/--
[stirling_bell_polynomial_connection_pair_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingBellPolynomialConnection.lean)
-/
@[path]
private lemma stirling_bell_polynomial_connection_pair_general_eq
  {α β x : ℝ}
  {n r : ℕ} :
-- imply
  let bellPolynomial : ℕ → ℝ → ℝ := by
-- proof
  apply MetaMathlibExt.stirling_bell_polynomial_connection_pair_general α β x n r

/--
[stirling_bell_polynomial_connection_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingBellPolynomialConnection.lean)
-/
@[path]
private lemma stirling_bell_polynomial_connection_pair_eq
  {α β x : ℝ}
  {n r : ℕ}
-- given
  (hβ : β ≠ 0) :
-- imply
  let bellPolynomial : ℕ → ℝ → ℝ := by
-- proof
  apply MetaMathlibExt.stirling_bell_polynomial_connection_pair α β x n r hβ


-- created on 2026-10-20
