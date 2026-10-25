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
import Theorem.Topology.Homotopy.BorsukUlam.Part7


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- The lift to the sphere (normalized). -/
noncomputable def buLift (n : ℕ) (x : Fin n → ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨‖buV n x‖⁻¹ • buV n x, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (buV_ne_zero x)⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
