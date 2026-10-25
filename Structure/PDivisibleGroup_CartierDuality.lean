import Mathlib
import Instance.PDivisibleGroup_Points
import Instance.HopfAlgebra_CartierDual
import Instance.HopfAlgebra_CartierDualInstances

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra WithConv

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

structure CartierDuality (G G' : PDivisibleGroup R p h) : Type where

  equiv : ∀ v, G'.level v ≃ₐc[R] CartierDual R (G.level v)

  equiv_transition : ∀ (v : ℕ) (x : G'.level (v + 1)) (a : G.level (v + 1)),
    equiv v (G'.transition v x) (G.transition v a) =
      equiv (v + 1) x (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p a)


namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')


variable (L : Type) [CommRing L] [Algebra R L]


end CartierDuality

end PDivisibleGroup

end
