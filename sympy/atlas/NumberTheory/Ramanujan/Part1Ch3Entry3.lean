/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Defs.Filter
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9Odd
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9Odd
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example4HarmonicPoissonAsymptotic

end Entry10Example4HarmonicPoissonAsymptotic

namespace Entry3

noncomputable def sector (ε : ℝ) : Set ℂ :=
  {z : ℂ | -Real.pi + ε ≤ Complex.arg z ∧ Complex.arg z ≤ Real.pi - ε}

noncomputable def fCoeff (x : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-x) * ∑' (k : ℕ), (((k + 1 : ℕ) : ℂ) ^ j * x ^ (k + 1) / (Nat.factorial k : ℂ))

noncomputable def psi (x z : ℂ) : ℂ :=
  ∑' (j : ℕ), if ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) = (0 : ℂ) then (0 : ℂ) else
      ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)))
end Entry3
namespace Entry3Fsummable
end Entry3Fsummable
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
