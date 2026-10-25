/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean -/

import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Projectivization.Independence
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

/-- An indexed family of affine points is in general position through dimension `d` if every
subfamily of at most `d + 1` points is affinely independent. -/
def IsGeneralPosition (k : Type u) [DivisionRing k] {V : Type v} {P : Type w} [AddCommGroup V]
    [Module k V] [AffineSpace V P] {ι : Type*} (d : ℕ) (p : ι → P) : Prop :=
  ∀ s : Finset ι, s.card ≤ d + 1 → AffineIndependent k (s.restrict p)

end Affine
end
