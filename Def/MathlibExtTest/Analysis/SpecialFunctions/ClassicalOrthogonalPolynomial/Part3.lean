/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ClassicalOrthogonalPolynomial.lean -/

module

public import Structure.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic
public import Theorem.MathlibExtTest.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial.Part3

@[expose] public section

namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

noncomputable def chebyshevFamily : ClassicalOrthogonalPolynomialFamily where
  P := monicChebyshev
  monic := monicChebyshev_monic
  natDegree_eq := monicChebyshev_natDegree
  μ := chebyshevMeasure
  domain := Set.Ioc (-1) 1
  measurable_domain := measurableSet_Ioc
  ordConnected_domain := ordConnected_Ioc
  interior_domain_nonempty := by
    rw [interior_Ioc]
    exact ⟨0, by norm_num⟩
  orthogonal := monicChebyshev_orthogonal_explicit
  norm_ne_zero := monicChebyshev_norm_ne_zero_explicit
  weight := chebyshevWeight
  weight_nonneg := fun x _ => chebyshevWeight_nonneg x
  measure_eq := rfl
  classical := chebyshevWeight_classical

end MetaMathlibExt
