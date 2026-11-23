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
public import Def.Combinatorics.Enumerative.Partition.RogersRamanujan.Part2
@[expose] public section

section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

noncomputable instance : DecidablePred rrGap2 := fun _ => Classical.propDecidable _

end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted
end
