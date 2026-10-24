/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/VanDerWaerden.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import sympy.atlas.Analysis.Complex.Hurwitz
import Lemma.Complex.Hurwitz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.MeanInequalities

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted

/-- H-stability: no zeros when every coordinate has positive real part. -/
private def vdw_HStable (k : ℕ) (q : MvPolynomial (Fin k) ℝ) : Prop :=
  ∀ z : Fin k → ℂ, (∀ i, 0 < (z i).re) → MvPolynomial.aeval z q ≠ 0

/-- Capacity bound: `c * ∏ x ≤ eval x q` on the positive orthant. -/
private def vdw_CapBound (k : ℕ) (q : MvPolynomial (Fin k) ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin k → ℝ, (∀ i, 0 < x i) → c * ∏ i, x i ≤ MvPolynomial.eval x q

/-- Full positivity of degree `d`: every degree-`d` coefficient is positive. -/
private def vdw_FullPos (k d : ℕ) (q : MvPolynomial (Fin k) ℝ) : Prop :=
  ∀ m : Fin k →₀ ℕ, Finsupp.degree m = d → 0 < q.coeff m

/-- The all-ones exponent. -/
private noncomputable def vdw_ones (k : ℕ) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm 1

/-- The `T` operator: `∂q/∂x₀` at `x₀ = 0`. -/
private noncomputable def vdw_T (k : ℕ) (q : MvPolynomial (Fin (k + 1)) ℝ) :
    MvPolynomial (Fin k) ℝ :=
  Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k q) 1

/-- The `D` operator: `∂q/∂x₀` in all variables, via `finSuccEquiv`. -/
private noncomputable def vdw_D (k : ℕ) (q : MvPolynomial (Fin (k + 1)) ℝ) :
    MvPolynomial (Fin (k + 1)) ℝ :=
  (MvPolynomial.finSuccEquiv ℝ k).symm
    (Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ k q))

/-- The product of column linear forms. -/
private noncomputable def vdw_p (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ j, ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i

/-- The Gurvits factor `g k = (k / (k + 1)) ^ k`. -/
private noncomputable def vdw_g (k : ℕ) : ℝ :=
  ((k : ℝ) / ((k : ℝ) + 1)) ^ k

end MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted
namespace MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted
private noncomputable def vdw_J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => (n : ℝ)⁻¹
end MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted
