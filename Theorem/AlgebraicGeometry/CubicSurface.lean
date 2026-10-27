import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Structure.AlgebraicGeometry.CubicSurface
/-!
# Cubic surfaces in ℙ³

A *cubic surface* is a degree-`3` hypersurface in projective `3`-space `ℙ³` over a field `k`.
We present such a surface by its **defining equation**: a nonzero homogeneous polynomial of
degree `3` in the four homogeneous coordinates `x₀, x₁, x₂, x₃`. The surface itself is the
projective zero locus `V(f) ⊆ ℙ³`.
-/


noncomputable section

namespace AlgebraicGeometry

open MvPolynomial

variable (k : Type*) [Field k]

namespace CubicSurface

variable {k}

/-- The defining cubic of a cubic surface has total degree exactly `3`. -/
theorem totalDegree_defining (S : CubicSurface k) : S.defining.totalDegree = 3 :=
  S.isHomogeneous.totalDegree S.defining_ne_zero

/-- Each partial derivative of the defining cubic is homogeneous of degree `2`. -/
theorem isHomogeneous_pderiv (S : CubicSurface k) (i : Fin 4) :
    (pderiv i S.defining).IsHomogeneous 2 :=
  S.isHomogeneous.pderiv

end CubicSurface
end AlgebraicGeometry
end
