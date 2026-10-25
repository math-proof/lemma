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
import Instance.Combinatorics.Enumerative.Partition.RogersRamanujan.Part2


section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

/-- Left card `A(N)`, literally the Wanted left card. -/
def rrA (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N =>
    p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b)).card

/-- Right card `B(N)`, literally the Wanted right card. -/
def rrB (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N =>
    ∀ m ∈ p.parts, m % 5 = 1 ∨ m % 5 = 4)).card

/-- Left generating series `FA`. -/
noncomputable def rrFA : PowerSeries ℚ :=
  PowerSeries.mk fun N => ((rrA N : ℕ) : ℚ)

/-- Right generating series `FB`. -/
noncomputable def rrFB : PowerSeries ℚ :=
  PowerSeries.mk fun N => ((rrB N : ℕ) : ℚ)

/-! ## right side and product identity -/

/-- Truncated good predicate for the finite `tprod` step. -/
def rrGoodLe (n m : ℕ) : Prop := rrGood m ∧ m ≤ 5 * n

end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted
end
