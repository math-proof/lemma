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
import Theorem.Topology.Homotopy.BorsukUlam.Part6


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Lift from the cube to the upper hemisphere -/

/-- The unnormalized lift `x ↦ (1 - ‖x‖, x)` into `ℝ^(n+1)`. -/
def buV (n : ℕ) (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) (1 - ‖x‖) x)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
