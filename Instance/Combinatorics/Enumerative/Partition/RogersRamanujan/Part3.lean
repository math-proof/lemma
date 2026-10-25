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
import Def.Combinatorics.Enumerative.Partition.RogersRamanujan.Part3


section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

instance rrGoodLe_dec (n : ℕ) : DecidablePred (rrGoodLe n) :=
  fun m => inferInstanceAs (Decidable (rrGood m ∧ m ≤ 5 * n))

end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted
end
