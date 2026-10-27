import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
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

/-- A cubic surface in `ℙ³` over `k`, presented by its defining equation: a nonzero homogeneous
polynomial of degree `3` in the four homogeneous coordinates. -/
@[ext]
structure CubicSurface where
  /-- The homogeneous cubic form cutting out the surface. -/
  defining : MvPolynomial (Fin 4) k
  /-- The defining form has degree `3`. -/
  isHomogeneous : defining.IsHomogeneous 3
  /-- The defining form is not identically zero. -/
  defining_ne_zero : defining ≠ 0

end AlgebraicGeometry
end
