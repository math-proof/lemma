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
public import Def.Topology.Homotopy.BorsukUlam.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- The difference map is continuous. -/
theorem buG_continuous {n : ℕ}
    {F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
    (hF : Continuous F) : Continuous (buG n F) := by
  have h1 : Continuous (fun x : Fin n → ℝ => F (buLift n x)) :=
    hF.comp buLift_continuous
  have h2 : Continuous (fun x : Fin n → ℝ => F (-buLift n x)) :=
    hF.comp (continuous_neg.comp buLift_continuous)
  have hsub : Continuous
      (fun x : Fin n → ℝ => F (buLift n x) - F (-buLift n x)) := h1.sub h2
  unfold buG
  exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp hsub

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
