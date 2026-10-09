import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.UnsignedCharlierPolynomialsOfOrder0

open MetaMathlibExt

/--
[unsignedCharlier_coeff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/UnsignedCharlierPolynomialsOfOrder0.lean)
-/
@[path]
private lemma unsignedCharlier_coeff_eq_eq
-- given
  (n m : ℕ) :
-- imply
  (unsignedCharlierOrder0 ℕ n).coeff m = unsignedCharlierCoeff n m := by
-- proof
  apply unsignedCharlier_coeff_eq


-- created on 2026-10-09
