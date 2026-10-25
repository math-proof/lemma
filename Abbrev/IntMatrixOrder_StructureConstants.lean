import Mathlib

set_option autoImplicit false

noncomputable section

open Matrix

namespace IntMatrixOrder

variable {G : Type*} {n K : ℕ} (T : G → Matrix (Fin n) (Fin n) ℤ) (u : Fin K → Matrix (Fin n) (Fin n) ℤ)
  (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ) (cT : G → Fin K → ℤ)

section AnyRing

variable (R' : Type*) [CommRing R']

abbrev uC (k : Fin K) : Matrix (Fin n) (Fin n) R' := (u k).map (Int.castRingHom R')

abbrev TC (g : G) : Matrix (Fin n) (Fin n) R' := (T g).map (Int.castRingHom R')

end AnyRing

section Descent

variable (R : Type*) [CommRing R] [CharZero R]

end Descent

section Basis

variable (R : Type*) [CommRing R]
variable (huind : LinearIndependent R (fun k : Fin K => (u k).map (Int.castRingHom R)))
  (huspan : Submodule.span R (Set.range fun k : Fin K => (u k).map (Int.castRingHom R)) =
    Subalgebra.toSubmodule (Algebra.adjoin R (Set.range fun g : G => (T g).map (Int.castRingHom R))))

abbrev AR : Subalgebra R (Matrix (Fin n) (Fin n) R) := Algebra.adjoin R (Set.range (TC T R))

end Basis

end IntMatrixOrder

end
