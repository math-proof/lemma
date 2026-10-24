/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example1Asymptotic.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Ramanujan's factorial-series asymptotic expansion

This file proves the inverse-factorial asymptotic expansion in Part I, Chapter 3,
Section 8, Example 1 of Ramanujan's notebooks.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example1Asymptotic

private def sec8Ex1Prod (k : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range k, (z + ((i + 1 : ℕ) : ℂ))

private noncomputable def sec8Ex1Term (a : ℕ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ j * a j / sec8Ex1Prod (j + 1) z

private def sec8Ex1Coeff (n k : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + k) * (Nat.stirlingSecond n k : ℂ)

private noncomputable def sec8Ex1Approx (k N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), sec8Ex1Coeff n k / z ^ n

private noncomputable def sec8Ex1Recip (k : ℕ) (z : ℂ) : ℂ :=
  1 / sec8Ex1Prod k z

private noncomputable def sec8Ex1FiniteApprox (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j * a j * sec8Ex1Approx (j + 1) (N + 1) z

private noncomputable def sec8Ex1Main (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    (-1 : ℂ) ^ j *
      (∑ k ∈ Finset.range (j + 1),
        a k * (Nat.stirlingSecond (j + 1) (k + 1) : ℂ)) / z ^ (j + 1)

private def sec8Ex1RealProd (x : ℝ) (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (j + 1), (x + ((k + 1 : ℕ) : ℝ))
end Section8Example1Asymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
