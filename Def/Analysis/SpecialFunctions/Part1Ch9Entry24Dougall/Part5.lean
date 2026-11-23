/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall.Part4

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def seqU : ℕ → ℂ := fun n => ((seqT n : ℝ) : ℂ)

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end
