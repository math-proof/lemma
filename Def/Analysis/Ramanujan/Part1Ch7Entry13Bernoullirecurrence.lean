/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry13Bernoullirecurrence.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
public import Theorem.Real.Part1Ch7Entry13Bernoullipolyadd
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry13Bernoullirecurrence

open scoped Nat Real BigOperators Interval ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

open Entry13Bernoullipolyadd (chapter7StieltjesApprox)

noncomputable section

def chapter7StieltjesLaurentTerm (c : ℕ → ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * (c k : ℂ) / (k.factorial : ℂ) * (s - 1) ^ k

noncomputable def SFun (m : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 m, ((n : ℂ) ^ (-s))

noncomputable def IFun (m : ℕ) (s : ℂ) : ℂ :=
  ∫ t in (1 : ℝ)..(m : ℝ), ((t : ℂ) ^ (-s))

noncomputable def EFun (m : ℕ) (s : ℂ) : ℂ :=
  SFun m s - IFun m s

noncomputable def JFun (j m : ℕ) (s : ℂ) : ℂ :=
  ∫ t in (1 : ℝ)..(m : ℝ), ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-s)))

noncomputable def HFun (m : ℕ) (s : ℂ) : ℂ := EFun (m + 1) s

def USet : Set ℂ := { s : ℂ | 0 < s.re }

noncomputable def GFun (s : ℂ) : ℂ :=
  EFun 1 s + ∑' n : ℕ, (EFun (n + 2) s - EFun (n + 1) s)

end
end Entry13Bernoullirecurrence
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
