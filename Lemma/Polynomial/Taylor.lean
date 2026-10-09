import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.Taylor

open Polynomial

/--
[existsUnique_taylor_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/Taylor.lean)
-/
@[path]
private lemma existsUnique_taylor_remainder_eq
  [CommRing k]
-- given
  (f : k[X]) (a : k) :
-- imply
  ∃! g : k[X],
    f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
      g * (X - C a) ^ 2 := by
-- proof
  apply existsUnique_taylor_remainder


-- created on 2026-10-09
