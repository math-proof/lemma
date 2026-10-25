/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.Exponential
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
