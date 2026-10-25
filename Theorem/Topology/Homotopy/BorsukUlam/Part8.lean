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
import Def.Topology.Homotopy.BorsukUlam.Part11


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- The lift to the sphere is continuous. -/
theorem buLift_continuous {n : ℕ} : Continuous (buLift n) := by
  have hsmul : Continuous (fun x : Fin n → ℝ => ‖buV n x‖⁻¹ • buV n x) :=
    Continuous.smul
      (Continuous.inv₀ buV_continuous.norm
        (fun x => norm_ne_zero_iff.mpr (buV_ne_zero x)))
      buV_continuous
  exact Continuous.subtype_mk hsmul _

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
