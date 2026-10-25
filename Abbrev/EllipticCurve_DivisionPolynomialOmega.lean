import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

namespace Universal

abbrev Poly : Type := MvPolynomial (Fin 5) ℤ

end Universal

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

end Map

end WeierstrassCurve

end
