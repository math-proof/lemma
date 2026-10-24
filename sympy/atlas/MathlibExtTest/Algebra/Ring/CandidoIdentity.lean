/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Ring/CandidoIdentity.lean -/


import sympy.atlas.Algebra.Ring.CandidoIdentity
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat


namespace MetaMathlibExt

-- Generality check: the theorem applies over any commutative semiring.
example {R : Type*} [CommSemiring R] (x y : R) :
    2 * (x ^ 4 + y ^ 4 + (x + y) ^ 4) = (x ^ 2 + y ^ 2 + (x + y) ^ 2) ^ 2 :=
  candido_identity x y

-- Concrete specialization over the integers.
example : 2 * ((1 : ℤ) ^ 4 + 2 ^ 4 + (1 + 2) ^ 4) =
    ((1 : ℤ) ^ 2 + 2 ^ 2 + (1 + 2) ^ 2) ^ 2 :=
  candido_identity (R := ℤ) 1 2

-- Natural-number specialization: the subtraction-free identity applies to `ℕ`.
example : 2 * ((1 : ℕ) ^ 4 + 2 ^ 4 + (1 + 2) ^ 4) =
    ((1 : ℕ) ^ 2 + 2 ^ 2 + (1 + 2) ^ 2) ^ 2 :=
  candido_identity (R := ℕ) 1 2

end MetaMathlibExt
