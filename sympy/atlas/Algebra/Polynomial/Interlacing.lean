/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/Interlacing.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import sympy.atlas.Algebra.Polynomial.RealRooted
import Lemma.Polynomial.RealRooted
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Largest roots and interlacing families

This file develops the univariate root-ordering facts used by the interlacing-family step in the
Marcus--Spielman--Srivastava argument.
-/

open scoped ComplexOrder NNReal

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
