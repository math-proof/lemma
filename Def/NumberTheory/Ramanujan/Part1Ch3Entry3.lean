/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Defs.Filter
public import Def.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import Theorem.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import Theorem.Nat.Ramanujan.Part1Ch3Entry9Odd
public import Def.NumberTheory.Ramanujan.Part1Ch3Entry9Odd
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Asymptotics.Arith
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


namespace Entry10Example4HarmonicPoissonAsymptotic

end Entry10Example4HarmonicPoissonAsymptotic

section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry3

noncomputable def sector (ε : ℝ) : Set ℂ :=
  {z : ℂ | -Real.pi + ε ≤ Complex.arg z ∧ Complex.arg z ≤ Real.pi - ε}

noncomputable def fCoeff (x : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-x) * ∑' (k : ℕ), (((k + 1 : ℕ) : ℂ) ^ j * x ^ (k + 1) / (Nat.factorial k : ℂ))

noncomputable def psi (x z : ℂ) : ℂ :=
  ∑' (j : ℕ), if ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) = (0 : ℂ) then (0 : ℂ) else
      ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)))

end Entry3
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
