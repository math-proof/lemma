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
import sympy.atlas.Combinatorics.Enumerative.GaussianBinomial
import Lemma.Finset.Enumerative.GaussianBinomial
section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

/-! ## Bailey kernel notation and unit facts -/

/-- `P(m)`: the finite q-Pochhammer at `Q = X`. -/
private noncomputable def rrP (m : ℕ) : PowerSeries ℚ := qPochFin PowerSeries.X m

/-- `ip(m)`: the inverse of `P(m)`. -/
private noncomputable def rrIp (m : ℕ) : PowerSeries ℚ := (rrP m)⁻¹

/-- `P5(m)`: the finite q-Pochhammer at `Q = X^5`. -/
private noncomputable def rrP5 (m : ℕ) : PowerSeries ℚ := qPochFin (PowerSeries.X ^ 5) m

/-- `ip5(m)`: the inverse of `P5(m)`. -/
private noncomputable def rrIp5 (m : ℕ) : PowerSeries ℚ := (rrP5 m)⁻¹

/-! ## Shared notation for the Bailey chain and products -/

/-- Folded Jacobi-triple-product summand. -/
private noncomputable def rrEps (c b r : ℕ) : PowerSeries ℚ :=
  if r = 0 then 1
  else (-1 : PowerSeries ℚ) ^ r
    * ((PowerSeries.X : PowerSeries ℚ) ^ (c * (r.choose 2) + b * r)
      + (PowerSeries.X : PowerSeries ℚ) ^ (c * (r.choose 2) + (c - b) * r))

/-- Unit summand `u(r) = ε(1, 0, r)`. -/
private noncomputable def rrU (r : ℕ) : PowerSeries ℚ := rrEps 1 0 r

/-- Theta summand `θ(r) = ε(5, 2, r)`. -/
private noncomputable def rrTheta (r : ℕ) : PowerSeries ℚ := rrEps 5 2 r

/-- Partial theta sum `T(n)`. -/
private noncomputable def rrT (n : ℕ) : PowerSeries ℚ :=
  ∑ r ∈ Finset.range (n + 1), rrTheta r

/-- Finite product side `Π5(n)`. -/
private noncomputable def rrPi5 (n : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.range n,
    ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 2))
      * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 3))
      * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 5)))

/-- Good residues `1, 4 mod 5`. -/
private def rrGood (m : ℕ) : Prop := m % 5 = 1 ∨ m % 5 = 4

private instance : DecidablePred rrGood := fun m =>
  inferInstanceAs (Decidable (m % 5 = 1 ∨ m % 5 = 4))

/-- Finite Euler factor `E(n)`. -/
private noncomputable def rrE (n : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.range (5 * n),
    (if rrGood (i + 1) then 1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1) else 1)

/-- Gap-2 condition on a finset. -/
private def rrGap2 (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a < b → a + 2 ≤ b

private noncomputable instance : DecidablePred rrGap2 := fun _ => Classical.propDecidable _

/-- Left card `A(N)`, literally the Wanted left card. -/
private def rrA (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N =>
    p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b)).card

/-- Right card `B(N)`, literally the Wanted right card. -/
private def rrB (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N =>
    ∀ m ∈ p.parts, m % 5 = 1 ∨ m % 5 = 4)).card

/-- Left generating series `FA`. -/
private noncomputable def rrFA : PowerSeries ℚ :=
  PowerSeries.mk fun N => ((rrA N : ℕ) : ℚ)

/-- Right generating series `FB`. -/
private noncomputable def rrFB : PowerSeries ℚ :=
  PowerSeries.mk fun N => ((rrB N : ℕ) : ℚ)

/-! ## right side and product identity -/

/-- Truncated good predicate for the finite `tprod` step. -/
private def rrGoodLe (n m : ℕ) : Prop := rrGood m ∧ m ≤ 5 * n

private instance rrGoodLe_dec (n : ℕ) : DecidablePred (rrGoodLe n) :=
  fun m => inferInstanceAs (Decidable (rrGood m ∧ m ≤ 5 * n))

/-- Truncated restricted-partition generating series. -/
private noncomputable def rrFB' (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun N => (((Nat.Partition.restricted N (rrGoodLe n)).card : ℕ) : ℚ)

section
open scoped PowerSeries.WithPiTopology
end
end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted
end
