/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf
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

def chapter5Entry2F (phi : ℝ[X]) (n : ℕ) : ℝ[X] :=
  phi +
    ∑ k ∈ Icc 1 n,
      Polynomial.C
          ((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
            (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) *
        (chapter5PolynomialShift (k : ℝ) phi +
          chapter5PolynomialShift (-(k : ℝ)) phi)

def chapter5Entry2MinusSolution (phi : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ range (phi.natDegree / 2 + 1),
    Polynomial.C (1 / ((2 * n + 1 : ℕ) : ℝ)) * chapter5Entry2F phi n

def chapter5Entry2PlusSolution (phi : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ range (phi.natDegree / 2 + 1),
    Polynomial.C ((Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ n) *
      chapter5Entry2F phi n

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
