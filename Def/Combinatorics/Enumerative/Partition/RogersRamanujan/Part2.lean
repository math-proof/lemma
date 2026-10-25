/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RogersRamanujan.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Instances.Rat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.GaussianBinomial
import Lemma.Finset.Enumerative.GaussianBinomial
import Instance.Combinatorics.Enumerative.Partition.RogersRamanujan


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
