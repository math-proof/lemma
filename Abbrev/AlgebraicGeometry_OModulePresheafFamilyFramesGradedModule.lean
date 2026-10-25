import Mathlib
import Structure.AlgebraicGeometry_OModulePresheafHom
import Instance.AlgebraicGeometry_ProjTwistDatum

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace OModulePresheaf

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  {q : P ⟶ Spec (.of A)}

section FramesCompat

end FramesCompat

section Ambient

variable (G : ℕ → OModulePresheaf q)

end Ambient

section Family

variable [IsAffineHom ι] (G : ℕ → OModulePresheaf q) {s : ℕ}
  (θ : Fin s → ∀ k : ℕ, AffHom (G k) (G (k + 1)))

abbrev framesChart (j : Fin (r + 1)) : P.affineOpens :=
  ⟨ProjSpace.pullbackChart ι j, ProjSpace.isAffineOpen_pullbackChart ι j⟩

abbrev framesOverlap (j l : Fin (r + 1)) : P.affineOpens :=
  ⟨ProjSpace.pullbackOverlap ι j l, ProjSpace.isAffineOpen_pullbackOverlap ι j l⟩

end Family

end OModulePresheaf

end AlgebraicGeometry

end
