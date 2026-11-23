/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RogersRamanujan.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.GaussianBinomial
public import Theorem.Finset.Enumerative.GaussianBinomial
public import Instance.Combinatorics.Enumerative.Partition.RogersRamanujan

@[expose] public section

section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

/-- Finite Euler factor `E(n)`. -/
noncomputable def rrE (n : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.range (5 * n),
    (if rrGood (i + 1) then 1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1) else 1)

/-- Gap-2 condition on a finset. -/
def rrGap2 (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a < b → a + 2 ≤ b

end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted
end
