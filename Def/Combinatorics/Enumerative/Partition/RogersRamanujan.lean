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


section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

/-! ## Bailey kernel notation and unit facts -/

/-- `P(m)`: the finite q-Pochhammer at `Q = X`. -/
noncomputable def rrP (m : ℕ) : PowerSeries ℚ := qPochFin PowerSeries.X m

/-- `ip(m)`: the inverse of `P(m)`. -/
noncomputable def rrIp (m : ℕ) : PowerSeries ℚ := (rrP m)⁻¹

/-- `P5(m)`: the finite q-Pochhammer at `Q = X^5`. -/
noncomputable def rrP5 (m : ℕ) : PowerSeries ℚ := qPochFin (PowerSeries.X ^ 5) m

/-- `ip5(m)`: the inverse of `P5(m)`. -/
noncomputable def rrIp5 (m : ℕ) : PowerSeries ℚ := (rrP5 m)⁻¹

/-! ## Shared notation for the Bailey chain and products -/

/-- Folded Jacobi-triple-product summand. -/
noncomputable def rrEps (c b r : ℕ) : PowerSeries ℚ :=
  if r = 0 then 1
  else (-1 : PowerSeries ℚ) ^ r
    * ((PowerSeries.X : PowerSeries ℚ) ^ (c * (r.choose 2) + b * r)
      + (PowerSeries.X : PowerSeries ℚ) ^ (c * (r.choose 2) + (c - b) * r))

/-- Unit summand `u(r) = ε(1, 0, r)`. -/
noncomputable def rrU (r : ℕ) : PowerSeries ℚ := rrEps 1 0 r

/-- Theta summand `θ(r) = ε(5, 2, r)`. -/
noncomputable def rrTheta (r : ℕ) : PowerSeries ℚ := rrEps 5 2 r

/-- Partial theta sum `T(n)`. -/
noncomputable def rrT (n : ℕ) : PowerSeries ℚ :=
  ∑ r ∈ Finset.range (n + 1), rrTheta r

/-- Finite product side `Π5(n)`. -/
noncomputable def rrPi5 (n : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.range n,
    ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 2))
      * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 3))
      * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 5)))

/-- Good residues `1, 4 mod 5`. -/
def rrGood (m : ℕ) : Prop := m % 5 = 1 ∨ m % 5 = 4

end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted
end
