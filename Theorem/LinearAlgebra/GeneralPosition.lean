/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean -/

import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Projectivization.Independence
import Def.LinearAlgebra.GeneralPosition
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

section Affine

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

section Examples

/-- The empty family is in general position in every dimension. -/
example (p : Empty → P) (d : ℕ) : IsGeneralPosition k d p :=
  (affineIndependent_of_subsingleton k p).isGeneralPosition d

/-- Two distinct affine points are in general position through dimension one. -/
example (p q : P) (hpq : p ≠ q) : IsGeneralPosition k 1 ![p, q] :=
  (affineIndependent_of_ne k hpq).isGeneralPosition 1

end Examples
end Affine
end
