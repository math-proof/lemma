/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Corollary2HarmonicSeries.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Star
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry2Corollary2HarmonicSeries

-- Retained only because the frozen target
-- `ramanujan_part1_ch3_entry2_corollary2_harmonic_series` is stated with it.
-- Every proof below is carried out with Mathlib's `_root_.harmonic` instead.
def harmonic (n : ℕ) : ℚ :=
  (Finset.range n).sum fun k => (1 : ℚ) / ((k + 1 : ℕ) : ℚ)

noncomputable def cauchyF (x : ℂ) (k : ℕ) : ℂ := x ^ k / (Nat.factorial k : ℂ)

noncomputable def cauchyG (x : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n - 1) * x ^ n / (((n : ℕ) : ℂ) * (Nat.factorial n : ℂ))

noncomputable def cauchyH (x : ℂ) (n : ℕ) : ℂ :=
  ((_root_.harmonic n : ℚ) : ℂ) * x ^ n / (Nat.factorial n : ℂ)

end Entry2Corollary2HarmonicSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
