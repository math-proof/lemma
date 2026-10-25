/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ClassicalOrthogonalPolynomial.lean -/


import Structure.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic


namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

example (F : ClassicalOrthogonalPolynomialFamily) (n : ℕ) : (F.P n).Monic :=
  F.monic n

example (F : ClassicalOrthogonalPolynomialFamily) (n : ℕ) : (F.P n).natDegree = n :=
  F.natDegree_eq n

example (F : ClassicalOrthogonalPolynomialFamily) (m n : ℕ) (h : m ≠ n) :
    MeasureTheory.integral F.μ
      (fun x => Polynomial.eval x (F.P m) * Polynomial.eval x (F.P n)) = 0 :=
  F.orthogonal m n h

example (F : ClassicalOrthogonalPolynomialFamily) (n : ℕ) :
    MeasureTheory.integral F.μ (fun x => (Polynomial.eval x (F.P n)) ^ 2) ≠ 0 :=
  F.norm_ne_zero n

example (F : ClassicalOrthogonalPolynomialFamily) :
    F.μ = (MeasureTheory.volume.restrict F.domain).withDensity
      (fun x => ENNReal.ofReal (F.weight x)) := F.measure_eq

example (F : ClassicalOrthogonalPolynomialFamily) : Set.OrdConnected F.domain :=
  F.ordConnected_domain

example (F : ClassicalOrthogonalPolynomialFamily) : (interior F.domain).Nonempty :=
  F.interior_domain_nonempty

example (F : ClassicalOrthogonalPolynomialFamily) :
    ∃ u0 u1 v0 v1 v2 : ℝ, (v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0) ∧
      ∀ x : ℝ, x ∈ interior F.domain →
        DifferentiableAt ℝ F.weight x ∧
          (v0 + v1 * x + v2 * x ^ 2) * deriv F.weight x =
            (u0 + u1 * x) * F.weight x :=
  F.classical

end MetaMathlibExt
