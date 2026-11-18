/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry9Bernoulligrowth.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Def.Analysis.Ramanujan.Part1Ch7PowerDifference
public import Theorem.Complex.Part1Ch7PowerDifference
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Basic
@[expose] public section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


noncomputable section

end
section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry9Bernoulligrowth

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

/-- Compatibility alias for the former `Entry9Bernoulligrowth.chapter7Admissible`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible` directly. -/
abbrev chapter7Admissible (x : ℂ) : Prop :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible x

/-- Compatibility alias for the former `Entry9Bernoulligrowth.chapter7PowerDifferenceTerm`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm`
directly. -/
noncomputable abbrev chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm r x j

/-- Compatibility alias for the former `Entry9Bernoulligrowth.chapter7PowerDifferenceSum`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceSum`
directly. -/
noncomputable abbrev chapter7PowerDifferenceSum (r x : ℂ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceSum r x

end Entry9Bernoulligrowth
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
