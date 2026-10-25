import Structure.AlgebraicGeometry_TwoChartCech
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Algebra.Subalgebra.Prod

set_option autoImplicit false

noncomputable section

open LaurentPolynomial

universe u

namespace TwoChartCech

variable (R : Type u) [CommRing R] {s : ℕ}

abbrev levalUnit (u : Rˣ) : R[T;T⁻¹] →+* R := LaurentPolynomial.eval₂ (RingHom.id R) u

end TwoChartCech

end
