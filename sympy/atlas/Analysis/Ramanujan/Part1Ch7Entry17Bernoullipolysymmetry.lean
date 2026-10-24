/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry17Bernoullipolysymmetry.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Phi
import sympy.atlas.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Lemma.Complex.Part1Ch7DirichletBeta
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry17Bernoullipolysymmetry

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open DirichletBeta

noncomputable section

def chapter7DirichletBetaTerm (s : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k / Complex.cpow (2 * k + 1 : ℕ) s

def chapter7DirichletBetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, chapter7DirichletBetaTerm s k

def chapter7Entry17Left (r : ℂ) : ℂ :=
  chapter7Phi r ⟨-1 / 4, by
      change (-1 : ℝ) < -1 / 4 ∧ (-1 / 4 : ℝ) < 0
      norm_num⟩ -
    chapter7Phi r ⟨-3 / 4, by
      change (-1 : ℝ) < -3 / 4 ∧ (-3 / 4 : ℝ) < 0
      norm_num⟩

def chapter7Entry17Right (r : ℂ) : ℂ :=
  2 * Complex.cos (Real.pi * r / 2) * chapter7EulerStar (r + 1) /
    Complex.cpow 4 (r + 1)

/-- The Dirichlet beta coefficients. -/
private def betaCoeff : ℕ → ℂ := fun n => chapter7BetaCharacter (n : ZMod 4)

/-- Step function of beta-coefficient partial sums, for the Mellin argument. -/
private def betaStepFunc : ℝ → ℂ :=
  Set.indicator (Set.Ioi (1 : ℝ)) (fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)

/-- The Mellin-side function, holomorphic on `Re s > 0`. -/
private def betaMellinFunc : ℂ → ℂ := fun s => s * mellin betaStepFunc (-s)
end
end Entry17Bernoullipolysymmetry
end MathlibExt.Analysis.Ramanujan.Part1Ch7
