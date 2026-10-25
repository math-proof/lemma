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
import Theorem.Topology.Homotopy.BorsukUlam.Part4


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## The Tucker graph -/

/-- Vertices: finsets of grid points lying in the box (hence a `Fintype`). -/
def bu_tkV (n m : ℕ) : Type :=
  { σ : Finset (Fin n → ℤ) // σ ∈ (bu_tkBox n m).powerset }

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
