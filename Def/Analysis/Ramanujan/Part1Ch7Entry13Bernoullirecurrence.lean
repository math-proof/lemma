/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry13Bernoullirecurrence.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Def.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
import Lemma.Real.Part1Ch7Entry13Bernoullipolyadd
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
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
