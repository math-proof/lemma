/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry11Qgammafunctional.lean -/

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
public import Def.Analysis.Ramanujan.Part1Ch8Entry12Qgammaintegers
public import Theorem.Complex.Part1Ch8Entry12Qgammaintegers
public import Theorem.Complex.Digamma
public import Theorem.Real.Digamma
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Def.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry11Qgammafunctional

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Digamma (z : ℂ) : ℂ :=
  deriv Complex.Gamma z / Complex.Gamma z

def chapter8PhiTerm (x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  2 / ((((k : ℂ) * x) ^ 3) - (k : ℂ) * x)

def chapter8Phi (x : ℂ) : ℂ :=
  1 + ∑' j : ℕ, chapter8PhiTerm x j

def U : Set ℂ := (Set.range ((↑) : ℤ → ℂ))ᶜ

def digTerm (j : ℕ) (w : ℂ) : ℂ :=
  1 / ((j + 1 : ℕ) : ℂ) - 1 / (w + ((j + 1 : ℕ) : ℂ))

def digF (w : ℂ) : ℂ :=
  Complex.digamma (w + 1) + (Real.eulerMascheroniConstant : ℂ)

def digG (w : ℂ) : ℂ :=
  ∑' j : ℕ, digTerm j w

end
end Entry11Qgammafunctional
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
