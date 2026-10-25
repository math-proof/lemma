import Mathlib
set_option autoImplicit false


namespace MvPolynomial.CrossingQuotient

inductive GlueIndex (e : ℕ) : Type
  | chart (i : Fin e) : GlueIndex e
  | overlap (i : Fin e) (h : (i : ℕ) + 1 < e) : GlueIndex e
  | torus (h : 0 < e) : GlueIndex e

end MvPolynomial.CrossingQuotient
