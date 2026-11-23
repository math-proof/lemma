/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Instance.Topology.Homotopy.BorsukUlam

@[expose] public section

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- Upward extensions with the same sign set (tight-chain counters). -/
noncomputable def bu_tkUp {n : ℕ} (m : ℕ)
    (σ : Finset (Fin n → ℤ)) : Finset (Fin n → ℤ) :=
  (bu_tkBox n m).filter fun v => v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) ⊆ bu_tkS σ

/-- Upward extensions gaining exactly the new sign `ℓ` (loose-chain counters). -/
noncomputable def bu_tkUpL {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ))
    (ℓ : Bool × Fin n) : Finset (Fin n → ℤ) :=
  (bu_tkBox n m).filter fun v => v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) = insert ℓ (bu_tkS σ)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
