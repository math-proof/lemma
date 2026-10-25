import Mathlib
import Inductive.IncidenceSystem_Var
import Structure.IncidenceSystem

set_option autoImplicit false

open MvPolynomial

namespace IncidenceSystem

variable (g e m' : ℕ) (A : Type*) [CommRing A]


variable {g e m' A}

abbrev R (g e m' : ℕ) (A : Type*) [CommRing A] := MvPolynomial (Var g e m') A

namespace Data

variable (D : Data g e m' A)

end Data

section Eval

variable (pt : Var g e m' → A)

end Eval

namespace Data

variable (D : Data g e m' A) {B : Type*} [CommRing B] (f : A →+* B)

end Data

end IncidenceSystem
