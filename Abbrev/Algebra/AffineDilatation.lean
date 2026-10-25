import Mathlib
import Def.Algebra.AffineDilatation
set_option autoImplicit false


noncomputable section

universe u

namespace AffineDilatation

variable {A : Type u} [CommRing A]

abbrev Ring (I : Ideal A) (a : A) : Type u :=
  ↥(subalgebra I a)

end AffineDilatation
end
