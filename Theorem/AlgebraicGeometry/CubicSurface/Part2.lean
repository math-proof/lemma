import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.AlgebraicGeometry.CubicSurface
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
end AlgebraicGeometry
end
