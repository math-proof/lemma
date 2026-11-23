/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry17Bernoullipolysymmetry.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch7Phi
public import Theorem.Analysis.Ramanujan.Part1Ch7DirichletBeta
public import Theorem.Complex.Part1Ch7DirichletBeta
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

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
def betaCoeff : ℕ → ℂ := fun n => chapter7BetaCharacter (n : ZMod 4)

/-- Step function of beta-coefficient partial sums, for the Mellin argument. -/
def betaStepFunc : ℝ → ℂ :=
  Set.indicator (Set.Ioi (1 : ℝ)) (fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)

/-- The Mellin-side function, holomorphic on `Re s > 0`. -/
def betaMellinFunc : ℂ → ℂ := fun s => s * mellin betaStepFunc (-s)

end
end Entry17Bernoullipolysymmetry
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
