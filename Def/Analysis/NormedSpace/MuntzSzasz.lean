/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

open scoped unitInterval


section

namespace FunctionalAnalysis.MuntzSzaszWanted

/-- The Golitschek operator: a linear operator on polynomials used in von Golitschek's
elementary proof of the sufficiency half of the Müntz–Szász theorem. -/
noncomputable def mszGol (lam : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P.sum fun j a =>
    Polynomial.C (a / ((lam : ℝ) - (j : ℝ))) * (Polynomial.X ^ j - Polynomial.X ^ lam)

end FunctionalAnalysis.MuntzSzaszWanted
end
