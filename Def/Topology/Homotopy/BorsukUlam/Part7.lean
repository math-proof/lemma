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
public import Instance.Topology.Homotopy.BorsukUlam.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- Door from `σ` to `τ`: `τ` adds one vertex and the old labels cover the new sign set. -/
def bu_tkDoor {n : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (σ τ : Finset (Fin n → ℤ)) : Prop :=
  ∃ v, v ∉ σ ∧ τ = insert v σ ∧ bu_tkS τ ⊆ σ.image L

/-- Adjacency on underlying finsets: doors either way, or the antipodal boundary edge. -/
def bu_tkAdj {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ τ : Finset (Fin n → ℤ)) : Prop :=
  bu_tkHappy m L σ ∧ bu_tkHappy m L τ ∧
    (bu_tkDoor L σ τ ∨ bu_tkDoor L τ σ ∨ (bu_tkBdry m σ ∧ τ = σ.image Neg.neg))

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
