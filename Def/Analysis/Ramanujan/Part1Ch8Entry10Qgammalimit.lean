/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry10Qgammalimit.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch8Entry9Qgamma
public import Theorem.Complex.Part1Ch8Entry9Qgamma
public import Theorem.Complex.Digamma
public import Theorem.Real.Digamma
public import Def.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry10Qgammalimit

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry10Kernel (x : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0
  else if u = 1 then -1 / x
  else
    ((1 - u : ℝ) : ℂ) /
      ((u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1))

-- Helper: the kernel formula on (0,1), without the endpoint cases.
def helper_formula (x : ℂ) (u : ℝ) : ℂ :=
  ((1 - u : ℝ) : ℂ) / ((u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1))

-- Step B: the kernel integral equals the digamma series, via geometric series.
def intExp2 (x : ℂ) (m : ℕ) : ℂ := -(((m : ℕ) : ℂ) + 1) * x

def intExp1 (x : ℂ) (m : ℕ) : ℂ := intExp2 x m - 1

def intTerm (x : ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ intExp1 x m - (u : ℂ) ^ intExp2 x m

def geomBase (x : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-x * (Real.log u : ℂ))

end
end Entry10Qgammalimit
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
