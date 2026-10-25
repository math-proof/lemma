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
import Theorem.Topology.Homotopy.BorsukUlam.Part8


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## The odd map from the lift -/

/-- The difference map `x ↦ F (lift x) - F (-lift x)`, read off in coordinates. -/
noncomputable def buG (n : ℕ)
    (F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (F (buLift n x) - F (-buLift n x)).ofLp i

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
