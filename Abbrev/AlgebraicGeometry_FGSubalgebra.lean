import Mathlib

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

abbrev FGSubalgebra : Type u := {A₀ : Subalgebra R A // A₀.FG}

namespace FGSubalgebra


end FGSubalgebra

end AlgebraicGeometry
