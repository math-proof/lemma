import Structure.AlgebraicGeometry_CoherentBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace CoherentBaseChange

structure FibreH0Family (T : Scheme.{u}) where

  G : ∀ (U : T.Opens), IsAffineOpen U → TwoTermComplex.{u, u} Γ(T, U)

  h0 : T → ℕ

  hglue : ∀ (U : T.Opens) (hU : IsAffineOpen U) (t : U),
    h0 t = (G U hU).fibreH0 (hU.primeIdealOf t)

end CoherentBaseChange
