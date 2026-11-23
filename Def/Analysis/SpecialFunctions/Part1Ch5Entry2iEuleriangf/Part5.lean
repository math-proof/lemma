/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf.Part4

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch5

namespace Entry2iEuleriangf

open scoped Nat Real BigOperators Interval Polynomial

open Finset

noncomputable section

noncomputable def psYpoly (N : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.range (N + 1), Polynomial.C (psC n) * Polynomial.X ^ n

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
