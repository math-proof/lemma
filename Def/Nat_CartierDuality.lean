module
public import Mathlib
public import Def.AlgHom_Points
public import Def.LinearMap_CartierDual
public import Instance.HopfAlgebra_CartierDualInstances
public import Structure.PDivisibleGroup_CartierDuality
set_option autoImplicit false


public section

noncomputable section

open Coalgebra Bialgebra WithConv

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}


def IsCartierDual (G G' : PDivisibleGroup R p h) : Prop := Nonempty (CartierDuality G G')

namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')

def toDualEquiv (v : ℕ) : G'.level v ≃ₗ[R] Module.Dual R (G.level v) :=
  (D.equiv v).toLinearEquiv.trans (CartierDual.toDual R (G.level v))

variable (L : Type) [CommRing L] [Algebra R L]

def pair (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : L :=
  ∑ i, Point.toAlgHom f (Module.Free.chooseBasis R (G.level v) i) *
    Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i))

end CartierDuality

end PDivisibleGroup

end
