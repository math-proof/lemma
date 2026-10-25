/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean -/

import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Projectivization.Independence
import Theorem.LinearAlgebra.GeneralPosition
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

/-- An indexed family of projective points is in general position through dimension `d` if every
subfamily of at most `d + 1` points is projectively independent. -/
def IsGeneralPosition {k : Type u} [DivisionRing k] {V : Type v} [AddCommGroup V] [Module k V]
    {ι : Type*} (d : ℕ) (p : ι → ℙ k V) : Prop :=
  ∀ s : Finset ι, s.card ≤ d + 1 → Independent (s.restrict p)

end Projectivization
end
