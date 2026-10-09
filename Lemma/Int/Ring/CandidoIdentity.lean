import Mathlib
import sympy.Basic
import sympy.Algebra.Ring.CandidoIdentity

open MetaMathlibExt

/--
[candido_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Ring/CandidoIdentity.lean)
-/
@[path]
private lemma candido_identity_eq
  [CommSemiring R]
-- given
  (x y : R) :
-- imply
  2 * (x ^ 4 + y ^ 4 + (x + y) ^ 4) = (x ^ 2 + y ^ 2 + (x + y) ^ 2) ^ 2 := by
-- proof
  apply candido_identity


-- created on 2026-10-09
