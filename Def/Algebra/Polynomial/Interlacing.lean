/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/Interlacing.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Def.Algebra.Polynomial.RealRooted.Part2
public import Theorem.Polynomial.RealRooted
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Algebra.Polynomial.RuleOfSigns

@[expose] public section

open scoped ComplexOrder NNReal

/-!
# Largest roots and interlacing families

This file develops the univariate root-ordering facts used by the interlacing-family step in the
Marcus--Spielman--Srivastava argument.
-/


namespace Polynomial

/-- `a` interlaces the two largest roots of `p`: one copy of the largest root lies above `a`,
and every remaining root lies below `a`. -/
def HasUpperInterlacingPoint (p : Polynomial ℂ) (a : ℝ) : Prop :=
  a ≤ p.maxRealRoot ∧
    ∀ z ∈ p.roots.erase (p.maxRealRoot : ℂ), z.re ≤ a

/-- A finite polynomial family has a common upper interlacing point when one real number lies
between the two largest roots of every member, with multiplicity. -/
def HasCommonUpperInterlacing {ι : Type*} (P : ι → Polynomial ℂ) : Prop :=
  ∃ a : ℝ, ∀ i, (P i).HasUpperInterlacingPoint a

end Polynomial
