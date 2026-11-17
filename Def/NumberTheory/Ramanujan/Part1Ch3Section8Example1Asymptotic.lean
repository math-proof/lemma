/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example1Asymptotic.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Group

@[expose] public section

/-!
# Ramanujan's factorial-series asymptotic expansion

This file proves the inverse-factorial asymptotic expansion in Part I, Chapter 3,
Section 8, Example 1 of Ramanujan's notebooks.
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example1Asymptotic

def sec8Ex1Prod (k : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range k, (z + ((i + 1 : ℕ) : ℂ))

noncomputable def sec8Ex1Term (a : ℕ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ j * a j / sec8Ex1Prod (j + 1) z

def sec8Ex1Coeff (n k : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + k) * (Nat.stirlingSecond n k : ℂ)

noncomputable def sec8Ex1Approx (k N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), sec8Ex1Coeff n k / z ^ n

noncomputable def sec8Ex1Recip (k : ℕ) (z : ℂ) : ℂ :=
  1 / sec8Ex1Prod k z

noncomputable def sec8Ex1FiniteApprox (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j * a j * sec8Ex1Approx (j + 1) (N + 1) z

noncomputable def sec8Ex1Main (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    (-1 : ℂ) ^ j *
      (∑ k ∈ Finset.range (j + 1),
        a k * (Nat.stirlingSecond (j + 1) (k + 1) : ℂ)) / z ^ (j + 1)

def sec8Ex1RealProd (x : ℝ) (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (j + 1), (x + ((k + 1 : ℕ) : ℝ))

end Section8Example1Asymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
