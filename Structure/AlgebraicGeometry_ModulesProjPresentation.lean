import Mathlib
import Instance.AlgebraicGeometry_ProjSpace

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry


namespace Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

structure ProjPresentation (M : X.Modules) (f : X ⟶ Spec (.of R)) (N : ℕ) where

  σ : Fin (N + 1) → Γ(M, ⊤)

  toProj : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

  toProj_π : toProj ≫ ProjSpace.π R N = f

  frame : ∀ (i : Fin (N + 1)) (V : X.Opens),
    V ≤ toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) →
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))

  app_ratio_smul : ∀ i j : Fin (N + 1),
    (toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) •
        M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ≤ ⊤)).op (σ i)
      = M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ≤ ⊤)).op (σ j)


end Scheme.Modules

namespace ProjSpace

variable (R : Type u) [CommRing R]


end ProjSpace

variable (R : Type u) [CommRing R]


end AlgebraicGeometry

end
