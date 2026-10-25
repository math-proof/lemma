/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Corollary2HarmonicSeries.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
