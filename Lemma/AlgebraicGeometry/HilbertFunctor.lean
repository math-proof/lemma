import Mathlib
import Def.AlgebraicGeometry_HilbertFunctor
import Structure.AlgebraicGeometry_HilbertFunctor

set_option autoImplicit false

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ}


variable (A n)


variable {A}

@[ext] theorem Point.ext {h : ℕ → ℕ} {P Q : Point A n h} (e : P.I = Q.I) : P = Q := by
  cases P; cases Q; cases e; rfl

end AlgebraicGeometry.HilbertFunctor
