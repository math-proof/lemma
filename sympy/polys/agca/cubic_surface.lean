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

namespace CubicSurface

variable {k}

/-- The defining cubic of a cubic surface has total degree exactly `3`. -/
theorem totalDegree_defining (S : CubicSurface k) : S.defining.totalDegree = 3 :=
  S.isHomogeneous.totalDegree S.defining_ne_zero

/-- Each partial derivative of the defining cubic is homogeneous of degree `2`. -/
theorem isHomogeneous_pderiv (S : CubicSurface k) (i : Fin 4) :
    (pderiv i S.defining).IsHomogeneous 2 :=
  S.isHomogeneous.pderiv

/-- A point `x` is a singular point of the affine cone over `S` when the defining cubic and all of
its partial derivatives vanish at `x`. -/
def IsSingularPoint (S : CubicSurface k) (x : Fin 4 → k) : Prop :=
  aeval x S.defining = 0 ∧ ∀ i, aeval x (pderiv i S.defining) = 0

/-- The Jacobian smoothness criterion: the coordinate origin is the only common zero of the
defining cubic and its partial derivatives. -/
def IsSmooth [IsAlgClosed k] (S : CubicSurface k) : Prop :=
  ∀ x : Fin 4 → k, S.IsSingularPoint x → x = 0

/-- Euler's identity: when `3` is invertible in `k`, the vanishing of every partial derivative of
the defining cubic at a point forces the cubic itself to vanish there. -/
theorem aeval_defining_eq_zero_of_pderiv (h3 : (3 : k) ≠ 0) (S : CubicSurface k)
    {x : Fin 4 → k} (hx : ∀ i, aeval x (pderiv i S.defining) = 0) :
    aeval x S.defining = 0 := by
  have euler := S.isHomogeneous.sum_X_mul_pderiv
  apply_fun aeval x at euler
  rw [map_sum, map_nsmul, nsmul_eq_mul] at euler
  simp only [map_mul, aeval_X, hx, mul_zero, Finset.sum_const_zero] at euler
  rw [Nat.cast_ofNat] at euler
  obtain h | h := mul_eq_zero.1 euler.symm
  · exact absurd h h3
  · exact h

/-- When `3` is invertible in `k`, a point is singular exactly when all partial derivatives of the
defining cubic vanish there; the equation `f = 0` is then automatic (Euler's identity). -/
theorem isSingularPoint_iff (h3 : (3 : k) ≠ 0) (S : CubicSurface k) (x : Fin 4 → k) :
    S.IsSingularPoint x ↔ ∀ i, aeval x (pderiv i S.defining) = 0 :=
  ⟨fun h => h.2, fun h => ⟨aeval_defining_eq_zero_of_pderiv h3 S h, h⟩⟩

end CubicSurface

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
