/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry34Zeta3doublesum.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Def.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
public import Theorem.Real.Part1Ch9Entry8Arcsin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry34Zeta3doublesum

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

open Entry8Arcsin (chapter9OddHarmonic)

noncomputable section

def chapter9Entry34LeftTerm (x : ℝ) (k : ℕ) : ℝ :=
  (x / (1 + x)) ^ (k + 1) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)

def chapter9Entry34RightTerm (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) ^ 2 *
      chapter9OddHarmonic (k + 1) * x ^ (k + 1) /
    ((2 * k + 1).factorial : ℝ)

def chapter9Central (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * n) * (n.factorial : ℝ) ^ 2 / ((((2 * n + 1).factorial : ℕ)) : ℝ)

def chapter9AltOddRecip (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) / ((2 * k + 1 : ℕ) : ℝ)

def chapter9AltOddRecipSq (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * (n.choose k : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)

def chapter9F1 (x : ℝ) (p : ℕ × ℕ) : ℝ :=
  (1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2))
    * (-1 : ℝ) ^ p.2
    * (((p.1 + p.2).choose p.1 : ℕ) : ℝ)
    * x ^ (p.1 + 1 + p.2)

def chapter9CoeffC (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * chapter9AltOddRecipSq n

def chapter9F2 (x : ℝ) (p : ℕ × ℕ) : ℝ :=
  chapter9CoeffC p.1 * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
    * (x / (1 + x)) ^ (p.1 + 1 + p.2)

end
end Entry34Zeta3doublesum
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
