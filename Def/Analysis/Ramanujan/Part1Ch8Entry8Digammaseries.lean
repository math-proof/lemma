/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Gamma.Digamma
public import Theorem.Complex.Digamma
public import Theorem.Real.Digamma

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry8Digammaseries

open scoped Nat Real BigOperators Interval

open Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Digamma (z : ℂ) : ℂ :=
  deriv Complex.Gamma z / Complex.Gamma z

def chapter8Entry8Term (a b : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j / (a + b * ((j + 1 : ℕ) : ℂ))

end
end Entry8Digammaseries
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
