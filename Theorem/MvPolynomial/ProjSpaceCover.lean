module

public import Theorem.MvPolynomial.ProjSpace
public import Theorem.Scheme.OrderedAffineCoverCech
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Notation.AlgebraicGeometry_ProjSpaceCover

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpaceCover


public theorem stdCover_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCover R n).U j = AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down) := rfl

end StdCover

section StdCoverPullback

variable {A : Type u} [CommRing A] {n : ℕ}
variable {W : Scheme.{u}}
  (ι : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]


public theorem stdCoverPullback_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCoverPullback ι).U j = ι ⁻¹ᵁ (stdCover A n).U j := rfl

end StdCoverPullback

end ProjSpace

end AlgebraicGeometry

end
