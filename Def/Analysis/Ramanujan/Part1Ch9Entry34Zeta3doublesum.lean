/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry34Zeta3doublesum.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
import Lemma.Real.Part1Ch9Entry8Arcsin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic
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
