import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorem.AlgebraicGeometry.CubicSurface
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

/-- A point `x` is a singular point of the affine cone over `S` when the defining cubic and all of
its partial derivatives vanish at `x`. -/
def IsSingularPoint (S : CubicSurface k) (x : Fin 4 → k) : Prop :=
  aeval x S.defining = 0 ∧ ∀ i, aeval x (pderiv i S.defining) = 0

/-- The Jacobian smoothness criterion: the coordinate origin is the only common zero of the
defining cubic and its partial derivatives. -/
def IsSmooth [IsAlgClosed k] (S : CubicSurface k) : Prop :=
  ∀ x : Fin 4 → k, S.IsSingularPoint x → x = 0

end CubicSurface
end AlgebraicGeometry
end
