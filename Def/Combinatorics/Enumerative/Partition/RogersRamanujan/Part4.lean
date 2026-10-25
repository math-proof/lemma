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
import Instance.Combinatorics.Enumerative.Partition.RogersRamanujan.Part3


section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

/-- Truncated restricted-partition generating series. -/
noncomputable def rrFB' (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun N => (((Nat.Partition.restricted N (rrGoodLe n)).card : ℕ) : ℚ)

end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted
end
