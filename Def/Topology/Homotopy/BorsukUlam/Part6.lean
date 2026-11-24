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
public import Theorem.Topology.Homotopy.BorsukUlam.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## The Tucker graph -/

/-- Vertices: finsets of grid points lying in the box (hence a `Fintype`). -/
def bu_tkV (n m : ℕ) : Type :=
  { σ : Finset (Fin n → ℤ) // σ ∈ (bu_tkBox n m).powerset }

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
