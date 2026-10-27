import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorem.AlgebraicGeometry.CubicSurface.Part2
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

section Examples

/-- The Fermat cubic surface `x₀³ + x₁³ + x₂³ + x₃³ = 0`. -/
noncomputable def fermatCubicSurface : CubicSurface k where
  defining := X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 + X 3 ^ 3
  isHomogeneous := by
    have h : ∀ i : Fin 4, ((X i : MvPolynomial (Fin 4) k) ^ 3).IsHomogeneous 3 := fun i => by
      simpa using (isHomogeneous_X k i).pow 3
    exact (((h 0).add (h 1)).add (h 2)).add (h 3)
  defining_ne_zero := by
    intro h
    have := congrArg (aeval (![1, 0, 0, 0] : Fin 4 → k)) h
    simp at this

/-- The triple hyperplane `x₀³ = 0`, a degenerate (non-reduced) boundary example. -/
noncomputable def triplePlane : CubicSurface k where
  defining := X 0 ^ 3
  isHomogeneous := by simpa using (isHomogeneous_X k 0).pow 3
  defining_ne_zero := pow_ne_zero 3 (X_ne_zero 0)

end Examples
end AlgebraicGeometry
end
