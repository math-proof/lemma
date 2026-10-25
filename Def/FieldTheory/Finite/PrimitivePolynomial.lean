/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
set_option autoImplicit false

open scoped Polynomial

/-!
# Primitive polynomials over finite fields

Reusable finite-field version of ATLAS Definition 3.14.
Distinct from `Polynomial.IsPrimitive`, which means primitive content.
-/


namespace Polynomial

variable {F : Type*} [Field F]

/-- Monic irreducible polynomial whose root has maximal order. -/
def IsPrimitivePolynomial [Finite F] (f : F[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧
    orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1

end Polynomial
