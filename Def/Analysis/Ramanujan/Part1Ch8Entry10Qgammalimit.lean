/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry10Qgammalimit.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Basic
import Def.Analysis.Ramanujan.Part1Ch8Entry9Qgamma
import Lemma.Complex.Part1Ch8Entry9Qgamma
import Lemma.Complex.Digamma
import Lemma.Real.Digamma
import Def.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
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
