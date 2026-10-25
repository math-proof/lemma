/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean -/

import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Projectivization.Independence
import Def.LinearAlgebra.GeneralPosition.Part2
/-!
# General position

This file defines general position for indexed families of points in affine and projective spaces.
A family is in general position through dimension `d` when each subfamily of at most `d + 1`
points is independent.
-/


noncomputable section

open Function

open scoped Affine LinearAlgebra.Projectivization

universe u v w

variable {k : Type u} {V : Type v} {P : Type w} {ι ι' : Type*}

namespace Projectivization

variable [DivisionRing k] [AddCommGroup V] [Module k V]

section Examples

/-- Two distinct projective points are in general position through dimension one. -/
example (p q : ℙ k V) (hpq : p ≠ q) : IsGeneralPosition 1 ![p, q] :=
  ((independent_pair_iff_ne p q).2 hpq).isGeneralPosition 1

end Examples
end Projectivization
end
