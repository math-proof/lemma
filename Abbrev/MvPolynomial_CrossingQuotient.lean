import Mathlib

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

variable (W : Type*) [CommRing W]

abbrev CrossingQuotient (t : W) : Type _ :=
  MvPolynomial (Fin 2) W ⧸ Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}

variable {W}

namespace CrossingQuotient

variable (t : W)

abbrev mk : MvPolynomial (Fin 2) W →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.mkₐ W (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)})

end CrossingQuotient

end MvPolynomial

end
