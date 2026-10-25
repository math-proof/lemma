/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Instance.Topology.Homotopy.BorsukUlam.Part3


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- Up-neighbors: one-vertex extensions whose new sign set is covered by old labels. -/
noncomputable def bu_upFin {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Finset (Finset (Fin n → ℤ)) :=
  ((bu_tkBox n m).filter fun v =>
    v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ σ.image L).image
    fun v => insert v σ

/-- Down-neighbors: one-vertex deletions still covering the sign set. -/
def bu_downFin {n : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Finset (Finset (Fin n → ℤ)) :=
  (σ.filter fun w =>
    (σ.erase w).Nonempty ∧ bu_tkS σ ⊆ (σ.erase w).image L).image
    fun w => σ.erase w

/-- Antipodal neighbor: the negation image when on the boundary. -/
noncomputable def bu_antiFin {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ)) :
    Finset (Finset (Fin n → ℤ)) :=
  if bu_tkBdry m σ then {σ.image Neg.neg} else ∅

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
