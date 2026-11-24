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
public import Def.Topology.Homotopy.BorsukUlam.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
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
