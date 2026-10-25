import Mathlib
import Inductive.IncidenceSystem_Var

set_option autoImplicit false

open MvPolynomial

namespace IncidenceSystem

variable (g e m' : ℕ) (A : Type*) [CommRing A]

structure Data where

  G : Fin g → Fin e → MvPolynomial (Option (Fin e)) A

  p : Option (Fin (g * m')) → Fin g → MvPolynomial (Option (Fin e)) A

  s : Option (Fin (g * m')) → Fin g → MvPolynomial (Option (Fin e)) A

  u₀ : Fin g → A

  w₀ : Fin g → Fin e → Fin (m' + 1) → A

  σ₀ : Option (Fin (g * m')) → Fin g → Fin (m' + 1) → A

variable {g e m' A}


namespace Data

variable (D : Data g e m' A)


end Data

section Eval

variable (pt : Var g e m' → A)


variable (D : Data g e m' A)


end Eval

namespace Data

variable (D : Data g e m' A) {B : Type*} [CommRing B] (f : A →+* B)


end Data

end IncidenceSystem
