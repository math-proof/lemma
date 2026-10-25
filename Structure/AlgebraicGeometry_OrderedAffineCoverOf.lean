import Mathlib

import Structure.AlgebraicGeometry_OModulePresheafHom
import Instance.AlgebraicGeometry_OrderedAffineCoverOf

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

structure Scheme.OrderedAffineCoverOf {V : Scheme.{u}} (W : V.Opens) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  le : ∀ i, U i ≤ W
  iSup_eq : ⨆ i, U i = W

attribute [instance] Scheme.OrderedAffineCoverOf.instFintype Scheme.OrderedAffineCoverOf.instLinearOrder

namespace Scheme.OrderedAffineCoverOf

variable {W : V.Opens} (K : V.OrderedAffineCoverOf W)


end Scheme.OrderedAffineCoverOf

namespace Scheme.OrderedAffineCover


end Scheme.OrderedAffineCover

namespace Scheme.OrderedAffineCoverOf

variable (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W)


end Scheme.OrderedAffineCoverOf


end AlgebraicGeometry

end
